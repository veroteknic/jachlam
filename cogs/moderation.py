"""Jachlam Moderation Cog — silence, Epstein quarantine, and role guard.

Only the moderation-specific prefix commands live here. Economy/system admin
prefix commands live in cogs/admin.py to keep each module focused.
"""

import time
import discord
from discord.ext import commands

from cogs import state as S


async def rogue_send(ctx, *args, **kwargs):
    command = getattr(ctx, 'command', None)
    command_name = getattr(command, 'name', '')
    if command_name in S.ROGUE_PROTECTED_COMMANDS:
        return await ctx.send(*args, **kwargs)
    should_corrupt = S.garble_mode or (S.rogue_mode and __import__('random').random() < S.rogue_intensity)
    if not should_corrupt:
        return await ctx.send(*args, **kwargs)
    from cogs.core import corrupt_send_payload
    send_args, send_kwargs = corrupt_send_payload(args, kwargs, full=S.garble_mode, add_insert=S.rogue_mode)
    return await ctx.send(*send_args, **send_kwargs)


async def check_gif_repeat(message):
    """If the configured user reposts a gif that's already been seen in the
    channel, timeout them for GIF_REPEAT_TIMEOUT_DAYS."""
    if S.ORION_USER_ID is None:
        return
    import re
    GIF_URL_PATTERN = re.compile('(https?://\\S+\\.(?:gif|gifv)\\S*|https?://(?:media\\.)?tenor\\.com/\\S+|https?://(?:media\\.)?giphy\\.com/\\S+|https?://(?:www\\.)?klipy\\.com/gifs/\\S+)', re.IGNORECASE)
    keys = []
    for attachment in message.attachments:
        name = (attachment.filename or '').lower()
        if name.endswith(('.gif', '.gifv', '.webp', '.mp4')) or 'gif' in (attachment.content_type or ''):
            keys.append(f'attach:{attachment.filename}:{attachment.size}')
    for match in GIF_URL_PATTERN.findall(message.content or ''):
        keys.append(f"url:{match.strip().split('?')[0].rstrip('/')}")
    for sticker in message.stickers:
        keys.append(f'sticker:{sticker.id}')
    if not keys:
        return
    if message.author.id != S.ORION_USER_ID:
        S.seen_gif_keys.update(keys)
        return
    repeats = [k for k in keys if k in S.seen_gif_keys]
    S.seen_gif_keys.update(keys)
    if not repeats:
        return
    member = message.author
    if not isinstance(member, discord.Member):
        return
    try:
        await member.timeout(__import__('datetime').timedelta(days=S.GIF_REPEAT_TIMEOUT_DAYS), reason="Reposted a gif that's already been used")
        await message.channel.send(f"{member.mention} reposted a gif that's already been used. timed out for {S.GIF_REPEAT_TIMEOUT_DAYS} days.")
    except discord.HTTPException as exc:
        S.debug(f'Failed to timeout {member.display_name} for gif repeat: {exc}')


class Moderation(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    # -------- Silence --------

    async def do_silence(self, guild, target):
        target_id = target.id if isinstance(target, discord.Member) else int(target)
        target_mention = target.mention if isinstance(target, discord.Member) else f'<@{target_id}>'
        if S.is_protected(target_id):
            return f'{target_mention} is protected and cannot be silenced.'
        if target_id in S.silenced_users:
            return f'{target_mention} is already silenced.'
        S.silenced_users.add(target_id)
        await S.save_silence_data()
        try:
            if guild is not None and list(getattr(guild, 'text_channels', []) or []):
                task = S.asyncio.create_task(self._warm_redact_webhooks(guild))
                S.background_tasks.append(task)
                task.add_done_callback(lambda t: S.background_tasks.remove(t) if t in S.background_tasks else None)
        except Exception as exc:
            S.debug(f'Redact warm dispatch failed: {exc}')
        return f'{target_mention} is now silenced. Their messages will be instantly replaced with `{S.SILENCE_REDACTED_TEXT}`.'

    async def do_unsilence(self, guild, target):
        target_id = target.id if isinstance(target, discord.Member) else int(target)
        target_mention = target.mention if isinstance(target, discord.Member) else f'<@{target_id}>'
        if target_id not in S.silenced_users:
            return f'{target_mention} is not silenced.'
        S.silenced_users.discard(target_id)
        await S.save_silence_data()
        return f'{target_mention} is unsilenced.'

    async def _get_redact_webhook(self, channel):
        cached = S.redact_webhooks.get(channel.id)
        if cached is not None:
            return cached
        try:
            webhooks = await channel.webhooks()
            for hook in webhooks:
                if hook.name == 'jachlam-redact' and hook.token is not None:
                    S.redact_webhooks[channel.id] = hook
                    return hook
            hook = await channel.create_webhook(name='jachlam-redact', reason='Silence redaction impersonation')
            S.redact_webhooks[channel.id] = hook
            return hook
        except (discord.Forbidden, discord.HTTPException, discord.NotFound) as exc:
            S.debug(f'Redact webhook unavailable in #{getattr(channel, "name", channel.id)}: {exc}')
            return None

    async def _warm_redact_webhooks(self, guild):
        if guild is None:
            return
        for channel in list(getattr(guild, 'text_channels', []) or []):
            try:
                await self._get_redact_webhook(channel)
            except Exception as exc:
                S.debug(f'Redact webhook warm failed in #{getattr(channel, "name", channel.id)}: {exc}')

    async def _repost_redaction(self, channel, webhook_channel, thread, display_name, avatar_url, author_mention):
        try:
            hook = await self._get_redact_webhook(webhook_channel) if isinstance(webhook_channel, discord.TextChannel) else None
            if hook is not None:
                kwargs = {'content': S.SILENCE_REDACTED_TEXT, 'username': display_name[:80] or 'redacted', 'avatar_url': avatar_url}
                if thread is not None:
                    kwargs['thread'] = thread
                await hook.send(**kwargs)
            else:
                await channel.send(f'{author_mention} {S.SILENCE_REDACTED_TEXT}')
        except (discord.Forbidden, discord.NotFound, discord.HTTPException) as exc:
            S.debug(f'Silence redact repost failed: {exc}')
            if isinstance(exc, discord.NotFound):
                S.redact_webhooks.pop(getattr(webhook_channel, 'id', None), None)
        except Exception as exc:
            S.debug(f'Silence redact repost failed: {type(exc).__name__}: {exc}')

    async def enforce_silence(self, message):
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        if getattr(message, 'webhook_id', None) is not None:
            return False
        if S.is_protected(getattr(author, 'id', 0)):
            return False
        if int(getattr(author, 'id', 0)) not in S.silenced_users:
            return False
        if message.guild is None:
            return False
        channel = message.channel
        webhook_channel = channel
        parent = getattr(channel, 'parent', None)
        if not isinstance(channel, discord.TextChannel) and parent is not None and isinstance(parent, discord.TextChannel):
            webhook_channel = parent
        display_name = getattr(author, 'display_name', getattr(author, 'name', 'unknown'))
        try:
            avatar_url = author.display_avatar.url if getattr(author, 'display_avatar', None) else None
        except Exception:
            avatar_url = None
        thread = None
        if isinstance(channel, discord.Thread):
            thread = channel
        try:
            try:
                await message.delete(reason='Silenced by moderator (!silence) -> redacted')
            except TypeError:
                await message.delete()
        except (discord.Forbidden, discord.NotFound, discord.HTTPException) as exc:
            S.debug(f'Silence delete failed: {exc}')
            return True
        try:
            task = S.asyncio.create_task(
                self._repost_redaction(channel, webhook_channel, thread, display_name, avatar_url, author.mention)
            )
            S.background_tasks.append(task)
            task.add_done_callback(lambda t: S.background_tasks.remove(t) if t in S.background_tasks else None)
        except Exception as exc:
            S.debug(f'Silence redact dispatch failed: {exc}')
        return True

    async def check_silence_commands(self, message):
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        content = (message.content or '').strip()
        if not content.startswith('!'):
            return False
        parts = content[1:].split(None, 1)
        name = parts[0].lower() if parts else ''
        arg = parts[1].strip() if len(parts) > 1 else ''
        if name not in ('silence', 'unsilence', 'unsilenced'):
            return False
        guild = message.guild
        if guild is None:
            try:
                await message.channel.send('Silence only works in a server.')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        if not S.can_manage_silence(author):
            try:
                await message.channel.send('not allowed')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        if name == 'silence' and arg.strip().casefold() in ('list', 'status'):
            try:
                if not S.silenced_users:
                    await message.channel.send('no one is silenced.')
                else:
                    await message.channel.send('silenced: ' + ', '.join(f'<@{uid}>' for uid in sorted(S.silenced_users)))
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        target = S.resolve_epstein_target(guild, arg)
        if target is None:
            try:
                await message.channel.send(f'usage: `!{name} @user` (mention or user ID).')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        try:
            if name == 'silence':
                await message.channel.send(await self.do_silence(guild, target))
            else:
                await message.channel.send(await self.do_unsilence(guild, target))
        except (discord.Forbidden, discord.HTTPException) as exc:
            S.debug(f'Silence command failed: {exc}')
            try:
                await message.channel.send('something went wrong applying that. check my permissions (Manage Messages).')
            except (discord.Forbidden, discord.HTTPException):
                pass
        return True

    # -------- Epstein quarantine --------

    async def apply_epstein_overwrites(self, guild, member):
        ok_count = 0
        fail_count = 0
        me = guild.me if guild is not None else None
        bot_perms = getattr(me, 'guild_permissions', None) if me is not None else None
        if bot_perms is not None and not (bot_perms.manage_roles or bot_perms.administrator):
            return (0, 0, True)
        channels = list(getattr(guild, 'text_channels', [])) + list(getattr(guild, 'voice_channels', []))
        for channel in channels:
            try:
                is_voice = channel.id != S.EPSTEIN_CHANNEL_ID and channel in getattr(guild, 'voice_channels', [])
                if channel.id == S.EPSTEIN_CHANNEL_ID:
                    await channel.set_permissions(member, send_messages=True, send_messages_in_threads=True,
                        create_public_threads=True, create_private_threads=True, add_reactions=True, view_channel=True,
                        reason='Epstein quarantine: allowed channel')
                elif is_voice:
                    await channel.set_permissions(member, send_messages=False, add_reactions=False, reason='Epstein quarantine')
                else:
                    await channel.set_permissions(member, send_messages=False, send_messages_in_threads=False,
                        create_public_threads=False, create_private_threads=False, add_reactions=False,
                        reason='Epstein quarantine')
                ok_count += 1
            except (discord.Forbidden, discord.HTTPException) as exc:
                fail_count += 1
                S.debug(f'Epstein overwrite failed in #{getattr(channel, "name", channel.id)}: {exc}')
            except Exception as exc:
                fail_count += 1
                S.debug(f'Epstein overwrite skipped in #{getattr(channel, "name", channel.id)}: {type(exc).__name__}: {exc}')
        for thread in getattr(guild, 'threads', []):
            try:
                if S.is_epstein_channel(thread):
                    continue
                await thread.set_permissions(member, send_messages=False, send_messages_in_threads=False,
                    add_reactions=False, reason='Epstein quarantine')
                ok_count += 1
            except (discord.Forbidden, discord.HTTPException):
                fail_count += 1
            except Exception as exc:
                fail_count += 1
                S.debug(f'Epstein thread overwrite skipped: {type(exc).__name__}: {exc}')
        return (ok_count, fail_count, False)

    async def clear_epstein_overwrites(self, guild, member):
        ok_count = 0
        fail_count = 0
        channels = list(getattr(guild, 'channels', []) or []) + list(getattr(guild, 'threads', []) or [])
        for channel in channels:
            try:
                overwrites = getattr(channel, 'overwrites_for', None)
                if overwrites is not None and member not in channel.overwrites:
                    continue
                await channel.set_permissions(member, overwrite=None, reason='Epstein quarantine lifted')
                ok_count += 1
            except (discord.Forbidden, discord.HTTPException):
                fail_count += 1
            except Exception:
                continue
        return (ok_count, fail_count)

    async def do_epstein_quarantine(self, guild, target):
        target_id = target.id if isinstance(target, discord.Member) else int(target)
        target_mention = target.mention if isinstance(target, discord.Member) else f'<@{target_id}>'
        if S.is_protected(target_id):
            return [f'{target_mention} is protected and cannot be Epstein-limited.']
        S.epstein_quarantined.add(target_id)
        await S.save_epstein_data()
        ok_count, fail_count, no_perms = (0, 0, False)
        if isinstance(target, discord.Member):
            ok_count, fail_count, no_perms = await self.apply_epstein_overwrites(guild, target)
        lines = [f'{target_mention} is now Epstein-limited to <#{S.EPSTEIN_CHANNEL_ID}> only.']
        if no_perms:
            lines.append('note: I lack **Manage Roles** so channel permissions were NOT changed -- enforcement is delete-only.')
        elif isinstance(target, discord.Member):
            lines.append(f'channel overwrites: {ok_count} set, {fail_count} failed.')
            if fail_count:
                lines.append('note: some overwrites failed (check my role position + Manage Roles). delete-enforcement is still active.')
        else:
            lines.append('note: user is not in this server, so no channel overwrites were set -- delete-enforcement will apply when they join/talk.')
        return lines

    async def do_epstein_release(self, guild, target):
        target_id = target.id if isinstance(target, discord.Member) else int(target)
        target_mention = target.mention if isinstance(target, discord.Member) else f'<@{target_id}>'
        S.epstein_quarantined.discard(target_id)
        S.epstein_warn_cooldown.pop(target_id, None)
        await S.save_epstein_data()
        if isinstance(target, discord.Member):
            ok_count, fail_count = await self.clear_epstein_overwrites(guild, target)
            return f'{target_mention} is released from Epstein quarantine. overwrites cleared: {ok_count}, failed: {fail_count}.'
        return f'{target_mention} is released from Epstein quarantine.'

    async def enforce_epstein_quarantine(self, message):
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        if S.is_protected(getattr(author, 'id', 0)):
            return False
        if int(getattr(author, 'id', 0)) not in S.epstein_quarantined:
            return False
        if message.guild is None:
            return False
        if S.is_epstein_channel(message.channel):
            return False
        try:
            try:
                await message.delete(reason='Epstein quarantine: user limited to <#1528950760962789426>')
            except TypeError:
                await message.delete()
        except (discord.Forbidden, discord.NotFound, discord.HTTPException) as exc:
            S.debug(f'Epstein delete failed: {exc}')
        now = time.monotonic()
        last_warn = S.epstein_warn_cooldown.get(author.id, 0)
        if now - last_warn >= 60:
            S.epstein_warn_cooldown[author.id] = now
            try:
                await message.channel.send(f'{author.mention} you are Epstein-limited to <#{S.EPSTEIN_CHANNEL_ID}> only.', delete_after=15)
            except (discord.Forbidden, discord.HTTPException):
                pass
        return True

    async def check_epstein_commands(self, message):
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        content = (message.content or '').strip()
        if not content.startswith('!'):
            return False
        parts = content[1:].split(None, 1)
        name = parts[0].lower() if parts else ''
        arg = parts[1].strip() if len(parts) > 1 else ''
        if name not in ('epsteinchannel', 'epstein', 'unepsteinchannel', 'unepstein'):
            return False
        guild = message.guild
        if guild is None:
            try:
                await message.channel.send('Epstein quarantine only works in a server.')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        if not S.can_manage_epstein(author):
            try:
                await message.channel.send('not allowed')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        target = S.resolve_epstein_target(guild, arg)
        if target is None:
            try:
                await message.channel.send(f'usage: `!{name} @user` (mention or user ID).')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        quarantining = name in ('epsteinchannel', 'epstein')
        try:
            if quarantining:
                await message.channel.send('\n'.join(await self.do_epstein_quarantine(guild, target)))
            else:
                await message.channel.send(await self.do_epstein_release(guild, target))
        except (discord.Forbidden, discord.HTTPException) as exc:
            S.debug(f'Epstein command failed: {exc}')
            try:
                await message.channel.send('something went wrong applying that. check my permissions and role position.')
            except (discord.Forbidden, discord.HTTPException):
                pass
        return True

    # -------- Role guard --------

    async def check_roleguard_command(self, message):
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        content = (message.content or '').strip()
        if not content.startswith('!'):
            return False
        name = content[1:].split(None, 1)[0].lower() if content[1:] else ''
        if name != 'roleguard':
            return False
        permissions = getattr(author, 'guild_permissions', None)
        if not (S.is_money_admin(author.id) or bool(permissions and permissions.administrator)):
            try:
                await message.channel.send('not allowed')
            except (discord.Forbidden, discord.HTTPException):
                pass
            return True
        try:
            from cogs.core import roleguard_status_text
            await message.channel.send(await roleguard_status_text(self.bot))
        except (discord.Forbidden, discord.HTTPException) as exc:
            S.debug(f'roleguard status failed: {exc}')
        return True


def find_shop_item(query):
    from cogs.shop import find_shop_item as _f
    return _f(query)


async def setup(bot):
    await bot.add_cog(Moderation(bot))
