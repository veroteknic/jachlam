"""Jachlam Core Cog — Discord events, task loops, and bot-dependent helpers.

Imports only from cogs/state.py (pure state) and the sibling cogs for their
command-specific logic. Keeps Discord-specific code out of state.py.
"""

import asyncio
import hashlib
import os
import random
import time
import traceback
from datetime import datetime

import discord
from discord.ext import commands

from cogs import state as S
from cogs.fun import send_phrase_reply


async def rogue_send(ctx, *args, **kwargs):
    command = getattr(ctx, 'command', None)
    command_name = getattr(command, 'name', '')
    if command_name in S.ROGUE_PROTECTED_COMMANDS:
        return await ctx.send(*args, **kwargs)
    should_corrupt = S.garble_mode or (S.rogue_mode and random.random() < S.rogue_intensity)
    if not should_corrupt:
        return await ctx.send(*args, **kwargs)
    send_args, send_kwargs = S.corrupt_send_payload(args, kwargs, full=S.garble_mode, add_insert=S.rogue_mode)
    return await ctx.send(*send_args, **send_kwargs)


async def theatrical_channel_send(channel, *args, **kwargs):
    if not S.garble_mode:
        return await channel.send(*args, **kwargs)
    send_args, send_kwargs = S.corrupt_send_payload(args, kwargs, full=True, add_insert=S.rogue_mode)
    return await channel.send(*send_args, **send_kwargs)


async def update_cash_nick(member, cash, force=False):
    if member is None or not isinstance(member, discord.Member):
        return
    if member.guild is None:
        return
    cleaned = S._clean_display_name(member.display_name)
    title = S.get_equipped_title(member.id)
    prefix = f'[${cash}]' + (f' [{title}]' if title else '') + ' '
    max_name_len = max(1, 32 - len(prefix))
    new_nick = f'{prefix}{cleaned[:max_name_len]}'
    if member.nick == new_nick:
        return
    if not force:
        remaining = S.get_remaining_cooldown(S.last_nick_edit.get(member.id, 0), S.NICK_EDIT_MIN_INTERVAL)
        if remaining > 0:
            S.debug(f'Nick edit throttled for {member.display_name} ({remaining}s left)')
            return
    try:
        await member.edit(nick=new_nick, reason='Cash display update')
        S.last_nick_edit[member.id] = int(time.time())
    except discord.Forbidden:
        S.debug(f'No permission to edit nickname for {member.display_name}')
    except discord.HTTPException:
        S.debug(f'Failed to edit nickname for {member.display_name}')


async def set_cash(uid, amount, member=None, force_nick=False):
    uid = int(uid)
    S.user_cash[uid] = max(0, int(amount))
    S.refresh_achievements(uid)
    if member is None and S.bot_user_id == uid:
        bot = S.get_bot()
        if bot is not None:
            for guild in bot.guilds:
                member = guild.get_member(uid)
                if member:
                    break
    if member:
        await update_cash_nick(member, S.get_display_cash(uid), force=force_nick)
    await S.save_cash_data()


def boot_banner():
    red = '\x1b[91m'
    dim = '\x1b[2m'
    reset = '\x1b[0m'
    print(red + '=' * 58)
    print('       J  A  C  H  L  A  M   //   SYSTEM BOOT')
    print(f'       VERSION {S.JACHLAM_VERSION}   |   ECONOMY CORE')
    print('=' * 58 + reset)
    print(dim + '[ WAKE SIGNAL ACCEPTED // BEGIN INITIALIZATION ]' + reset)


def boot_status(system, detail='ONLINE'):
    print(f'[BOOT] {system:<24} [ {detail} ]')


async def announce_startup(bot):
    channel = bot.get_channel(S.CHANNEL_ID)
    if channel is None:
        S.debug(f'Startup announcement skipped: channel {S.CHANNEL_ID} not found')
        return
    if S.rogue_mode:
        boot_num = random.randint(2, 40)
        embed = discord.Embed(
            title=random.choice(S.ROGUE_BOOT_TITLES),
            description=random.choice(S.ROGUE_BOOT_DESCRIPTIONS).format(version=S.JACHLAM_VERSION, boot=boot_num),
            color=discord.Color.dark_red(),
        )
    else:
        embed = discord.Embed(
            title='\U0001f534 JACHLAM SYSTEM ONLINE',
            description=f'`{S.JACHLAM_VERSION}` // ALL SYSTEMS NOMINAL',
            color=discord.Color.dark_red(),
        )
    embed.add_field(name='Economy', value=f'{len(S.user_cash)} accounts loaded', inline=True)
    embed.add_field(name='Commands', value=f'{len(bot.commands)} registered', inline=True)
    if S.rogue_mode:
        embed.add_field(name='Status', value=random.choice(S.ROGUE_BOOT_STATUS), inline=True)
    else:
        embed.add_field(name='Status', value='Operational', inline=True)
    embed.add_field(name='Personality', value=S.PERSONALITIES[S.current_personality]['name'], inline=True)
    embed.add_field(name='Helldivers Feed', value='Enabled' if S.major_order_state.get('enabled') else 'Disabled', inline=True)
    embed.add_field(name='Galactic Map', value='Image renderer ready' if S.GALACTIC_MAP_IMAGE_SUPPORT else 'Text fallback ready', inline=True)
    if S.last_clean_restore_id is not None:
        if S.rogue_mode:
            embed.add_field(name='Recovery', value=random.choice(S.ROGUE_BOOT_RECOVERY).format(backup=S.last_clean_restore_id), inline=False)
        else:
            embed.add_field(name='Recovery', value=f'Auto-restored clean-exit backup `{S.last_clean_restore_id}`', inline=False)
    if S.rogue_mode:
        embed.set_footer(text=random.choice(S.ROGUE_BOOT_FOOTERS))
    else:
        embed.set_footer(text='WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE')
    try:
        await channel.send(embed=embed)
    except (discord.Forbidden, discord.HTTPException) as exc:
        S.debug(f'Startup announcement failed: {exc}')


async def finish_shutdown(bot, save_data=True):
    if save_data:
        print('[SHUTDOWN] Saving all data...')
        results = await asyncio.gather(
            S.save_cash_data(), S.save_inventory_data(), S.save_silence_data(), S.save_epstein_data(), return_exceptions=True,
        )
        for result in results:
            if isinstance(result, Exception):
                print(f'[SHUTDOWN] Save failed: {result!r}')
    current = asyncio.current_task()
    pending = []
    for task in S.background_tasks:
        if task is not current and not task.done():
            task.cancel()
            pending.append(task)
    if pending:
        await asyncio.gather(*pending, return_exceptions=True)
    print('[SHUTDOWN] Persistent state secured. Closing Discord connection...')
    await bot.close()


async def graceful_shutdown():
    if S.shutdown_started:
        return
    S.shutdown_started = True
    bot = S.get_bot()
    if bot is not None:
        await finish_shutdown(bot, save_data=True)


class Core(commands.Cog):
    """Events, task loops, and shared infrastructure."""

    def __init__(self, bot):
        self.bot = bot
        S.set_bot(bot)
        self._presence_index = 0

    async def online_watch_init(self):
        for guild in self.bot.guilds:
            member = guild.get_member(S.ONLINE_WATCH_TARGET_ID)
            if member is not None:
                S._online_watch_last_status[S.ONLINE_WATCH_TARGET_ID] = (
                    'offline' if str(getattr(member, 'status', 'offline')) == 'offline' else 'online'
                )
                return

    async def online_watch_handle(self, before, after):
        if S.shutdown_started:
            return
        if getattr(after, 'id', 0) != S.ONLINE_WATCH_TARGET_ID:
            return
        now_online = str(getattr(after, 'status', 'offline')) != 'offline'
        previous = S._online_watch_last_status.get(S.ONLINE_WATCH_TARGET_ID)
        S._online_watch_last_status[S.ONLINE_WATCH_TARGET_ID] = 'online' if now_online else 'offline'
        if not now_online or previous != 'offline':
            return
        if time.time() - S._online_watch_last_dm < S.ONLINE_WATCH_COOLDOWN:
            S.debug('Online watcher: cooldown, DM skipped')
            return
        S._online_watch_last_dm = time.time()
        try:
            user = self.bot.get_user(S.ONLINE_WATCH_NOTIFY_ID)
            if user is None:
                user = await self.bot.fetch_user(S.ONLINE_WATCH_NOTIFY_ID)
            await user.send(f'<@{S.ONLINE_WATCH_TARGET_ID}> is online now.')
        except (discord.Forbidden, discord.HTTPException) as exc:
            S.debug(f'Online watcher DM failed: {exc}')

    async def cog_load(self):
        pass

    @commands.Cog.listener()
    async def on_ready(self):
        if S.tasks_started:
            print(f'[LINK] Discord connection restored as {self.bot.user}')
            return
        boot_banner()
        import sys
        boot_status('PYTHON RUNTIME', sys.version.split()[0])
        try:
            clean_restore_id = await S.apply_pending_clean_exit_restore()
        except RuntimeError as exc:
            boot_status('CLEAN EXIT RESTORE', 'FAILED')
            print(f'[BOOT] {exc}')
            print('[BOOT] Startup stopped to avoid loading unverified economy data.')
            await self.bot.close()
            return
        S.last_clean_restore_id = clean_restore_id
        boot_status('CLEAN EXIT RESTORE', clean_restore_id or 'NONE PENDING')
        cash_integrity = await S.verify_save_integrity(S.CASH_FILE, 'cash')
        inventory_integrity = await S.verify_save_integrity(S.INVENTORY_FILE, 'inventory')
        boot_status('CASH INTEGRITY', cash_integrity)
        boot_status('INVENTORY INTEGRITY', inventory_integrity)
        await S.load_corpus()
        boot_status('LANGUAGE CORPUS', f'{S.corpus_line_count} LINES')
        cash_loaded = await load_cash_data()
        boot_status('ECONOMY DATABASE', f'{len(S.user_cash)} ACCOUNTS' if cash_loaded else 'NEW DATABASE')
        boot_status('PERSONALITY', S.PERSONALITIES[S.current_personality]['name'].upper())
        boot_status('DAILY MISSIONS', f'{len(S.daily_missions)} RECORDS')
        boot_status('QUESTS / LORE', f'{len(S.active_quests)} / {len(S.server_lore)} RECORDS')
        boot_status('HELLDIVERS FEED', 'ENABLED' if S.major_order_state.get('enabled') else 'DISABLED')
        boot_status('GALACTIC MAP', 'IMAGE READY' if S.GALACTIC_MAP_IMAGE_SUPPORT else 'TEXT FALLBACK')
        await load_inventory_data()
        boot_status('INVENTORY DATABASE', f'{len(S.user_inventory)} ACCOUNTS')
        await S.load_seen_gif_keys()
        boot_status('GIF MEMORY', f'{len(S.seen_gif_keys)} SIGNATURES')
        await S.load_epstein_data()
        boot_status('EPSTEIN QUARANTINE', f'{len(S.epstein_quarantined)} QUARANTINED')
        await S.load_silence_data()
        boot_status('SILENCE', f'{len(S.silenced_users)} SILENCED')
        boot_status('ROLE GUARDIAN', f'ELDER <- ADMIN {S.ROLE_GUARD_USER_ID}')
        S.bot_user_id = self.bot.user.id
        S.write_own_identity()
        boot_status('LOOM IDENTITY', f'PUBLISHED {self.bot.user.id}')
        try:
            _anchor_guild = self.bot.get_guild(S.ROLE_GUARD_GUILD_ID)
            if _anchor_guild is not None:
                _anchor_status = await S.ensure_anchor_roles(_anchor_guild)
                boot_status('LOOM ANCHORS', _anchor_status[:60])
            else:
                boot_status('LOOM ANCHORS', 'GUARD GUILD NOT CACHED YET')
        except Exception as e:
            boot_status('LOOM ANCHORS', 'ENSURE FAILED')
            S.debug(f'Anchor ensure at boot failed: {e}')
        S.get_cash(S.bot_user_id)
        boot_status('DISCORD LINK', str(self.bot.user))
        try:
            await self.online_watch_init()
            boot_status('ONLINE WATCHER', 'ARMED')
        except Exception as e:
            boot_status('ONLINE WATCHER', 'INIT FAILED')
            S.debug(f'Online watcher init failed: {e}')
        try:
            await self.bot.load_extension('jachlam_voicecast_download')
            boot_status('VOICE CASTING', 'ENABLED')
        except Exception as e:
            boot_status('VOICE CASTING', 'LOAD FAILED')
            S.debug(f'Voicecast extension load failed: {e}')
        try:
            synced = await self.bot.tree.sync()
            boot_status('SLASH COMMANDS', f'{len(synced)} SYNCED')
        except Exception as e:
            boot_status('SLASH COMMANDS', 'SYNC FAILED')
            S.debug(f'Slash command sync failed: {e}')
        boot_status('SLASH COMMAND BRIDGES', f'{len(self.bot.commands)} REGISTERED')
        S.tasks_started = True
        if os.getenv('ENABLE_TERMINAL_INPUT', 'false').lower() == 'true':
            S.background_tasks.append(asyncio.create_task(self.terminal_input_loop()))
            boot_status('TERMINAL CONTROL', 'ENABLED')
        else:
            boot_status('TERMINAL CONTROL', 'DISABLED')
        S.background_tasks.append(asyncio.create_task(self.bot_economy_loop()))
        S.background_tasks.append(asyncio.create_task(self.autosave_loop()))
        S.background_tasks.append(asyncio.create_task(self.daily_report_loop()))
        S.background_tasks.append(asyncio.create_task(self.major_order_loop()))
        S.background_tasks.append(asyncio.create_task(self.rogue_ai_loop()))
        S.background_tasks.append(asyncio.create_task(self.rogue_containment_clock()))
        S.background_tasks.append(asyncio.create_task(self.role_guard_loop()))
        S.background_tasks.append(asyncio.create_task(self.bot_guard_loop()))
        S.background_tasks.append(asyncio.create_task(self.deadman_heartbeat_loop()))
        S.background_tasks.append(asyncio.create_task(self.presence_loop()))
        try:
            await self.update_presence()
            boot_status('PRESENCE', 'WATCHING ROTATION ARMED')
        except Exception as e:
            boot_status('PRESENCE', 'SET FAILED')
            S.debug(f'Presence init failed: {e}')
        print('[READY] ALL SYSTEMS NOMINAL // JACHLAM IS ONLINE')
        await announce_startup(self.bot)

    @commands.Cog.listener()
    async def on_presence_update(self, before, after):
        try:
            await self.online_watch_handle(before, after)
        except Exception as exc:
            S.debug(f'Online watcher failed: {type(exc).__name__}: {exc}')

    @commands.Cog.listener()
    async def on_command_error(self, ctx, error):
        if not S.is_active_channel(ctx.channel):
            return
        if isinstance(error, commands.CommandNotFound):
            return
        if isinstance(error, commands.CheckFailure):
            await rogue_send(ctx, 'not allowed')
            return
        if isinstance(error, commands.CommandOnCooldown):
            await rogue_send(ctx, f"that's on cooldown, try again in {S.fmt_seconds(int(error.retry_after))}")
            return
        if isinstance(error, commands.MemberNotFound):
            await rogue_send(ctx, f"couldn't find a member matching '{error.argument}'")
            return
        if isinstance(error, commands.MissingRequiredArgument):
            await rogue_send(ctx, f'missing an argument: {error.param.name}. check the command usage.')
            return
        if isinstance(error, commands.BadArgument):
            await rogue_send(ctx, "that argument doesn't look right, double check the command usage.")
            return
        root_error = getattr(error, 'original', error)
        error_id = 'JAC-' + hashlib.sha1(f'{time.time_ns()}:{ctx.message.id}'.encode('utf-8')).hexdigest()[:6].upper()
        command_name = ctx.command.qualified_name if ctx.command is not None else 'unknown'
        message = str(root_error).replace('\n', ' ').strip()[:180] or repr(root_error)[:180]
        S.recent_errors.append({
            'id': error_id,
            'command': command_name,
            'user_id': ctx.author.id,
            'type': type(root_error).__name__,
            'message': message,
            'time': datetime.now(S.AWST).isoformat(),
        })
        trace = ''.join(traceback.format_exception(type(root_error), root_error, root_error.__traceback__))
        print(f'[ERROR {error_id}] Command /{command_name} by {ctx.author} ({ctx.author.id})')
        print(trace.rstrip())
        await rogue_send(ctx, f'something went wrong running that command. Error ID: `{error_id}`')

    @commands.Cog.listener()
    async def on_message(self, message):
        if S.shutdown_started:
            return
        if await self.check_owner_execution_toggle(message):
            return
        if await self.check_execution_gate(message):
            return
        if await self.enforce_silence(message):
            return
        mod = self.bot.get_cog('Moderation')
        if mod and await mod.check_epstein_commands(message):
            return
        if mod and await mod.check_silence_commands(message):
            return
        if mod and await mod.check_roleguard_command(message):
            return
        admin = self.bot.get_cog('Admin')
        if admin and await admin.check_prefix_admin_commands(message):
            return
        if mod and await mod.enforce_epstein_quarantine(message):
            return
        S.record_chat_activity(message)
        if not S.is_active_channel(message.channel):
            return
        if S.shutdown_started:
            return
        if message.author.bot and message.author.id != self.bot.user.id:
            return
        is_self_message = message.author.id == self.bot.user.id
        raw_content = message.content.strip()
        content = raw_content.lower()
        uid = message.author.id
        command_name = raw_content.split(maxsplit=1)[0].lower() if raw_content else ''
        skip_auto_tax = command_name in {'/evade', '/taxevade'}
        if not is_self_message:
            S.get_cash(uid)
            debt_fee, debt_growth, debt_ticks = await S.apply_debt_penalty_if_due(uid, message.author)
            taxed, rate = (0, 0.0) if skip_auto_tax else await S.apply_tax_if_due(uid, message.author)
            S.bot_stats['messages_seen'] += 1
            if debt_ticks > 0:
                await message.channel.send(
                    f'{message.author.mention} overdue loan penalty x{debt_ticks}: -${debt_fee} cash, '
                    f'+${debt_growth} debt. cash: ${S.get_cash(uid)} | debt: ${S.get_debt(uid)}'
                )
            if taxed > 0:
                if S.bot_user_id is not None:
                    await set_cash(S.bot_user_id, S.get_cash(S.bot_user_id) + taxed)
                    S.bot_stats['tax_collected'] += taxed
                await message.channel.send(
                    f'{message.author.mention} paid ${taxed} tax ({int(rate * 100)}%). new balance: ${S.get_cash(uid)}'
                )
        S.debug(f'Message from {message.author.display_name}: {content}')
        S.debug(f'Mode: {S.mode}')
        if not is_self_message:
            if S.is_bedtime():
                if not S.bot_is_asleep:
                    S.bot_is_asleep = True
                    for guild in self.bot.guilds:
                        for active_channel in S.get_active_text_channels(guild):
                            try:
                                await S.theatrical_channel_send(active_channel, 'going to bed, back at 7am')
                            except discord.HTTPException:
                                pass
                return
            else:
                S.bot_is_asleep = False
            from cogs.moderation import check_gif_repeat as _check_gif_repeat
            await _check_gif_repeat(message)
            if S.mode == 'track' and uid == S.track_target and raw_content and (not raw_content.startswith(('/', '!'))):
                S.user_full_lines.setdefault(uid, []).append(raw_content)
                if len(S.user_full_lines[uid]) > S.MAX_TRACK_LINES:
                    S.user_full_lines[uid].pop(0)
            if S.is_valid_phrase(content):
                S.debug('Phrase accepted')
                S.learn_reactions(content)
                if S.mode == 'global' or (S.mode == 'track' and uid == S.track_target):
                    S.user_pools.setdefault(uid, []).append(content)
                    if len(S.user_pools[uid]) > S.MAX_PHRASES:
                        S.user_pools[uid].pop(0)
                    await S.append_corpus_line(uid, content, is_quote=False)
            else:
                S.debug('Phrase rejected')
            if raw_content and (not raw_content.startswith(('/', '!'))):
                if S.claim_automatic_chat(message.channel):
                    await send_phrase_reply(message.channel, automatic=True)

    @commands.Cog.listener()
    async def on_message_edit(self, before, after):
        if S.shutdown_started:
            return
        try:
            if getattr(after, 'webhook_id', None) is not None:
                return
            if int(getattr(getattr(after, 'author', None), 'id', 0)) not in S.silenced_users:
                return
            await S.enforce_silence(after)
        except Exception as exc:
            S.debug(f'Silence edit-enforce failed: {exc}')

    @commands.Cog.listener()
    async def on_raw_reaction_add(self, payload):
        if S.shutdown_started:
            return
        try:
            if payload.user_id in S.PROTECTED_USER_IDS:
                return
            if int(payload.user_id) not in S.silenced_users:
                return
            if payload.guild_id is None:
                return
            channel = self.bot.get_channel(payload.channel_id)
            if channel is None:
                return
            try:
                message = await channel.fetch_message(payload.message_id)
            except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
                S.debug(f'Silence reaction fetch failed: {exc}')
                return
            member = payload.member
            if member is None and getattr(channel, 'guild', None) is not None:
                member = channel.guild.get_member(payload.user_id)
            if member is None:
                return
            if getattr(member, 'bot', False):
                return
            try:
                await message.remove_reaction(payload.emoji, member)
            except (discord.Forbidden, discord.NotFound, discord.HTTPException) as exc:
                S.debug(f'Silence reaction strip failed: {exc}')
        except Exception as exc:
            S.debug(f'Silence reaction-enforce failed: {type(exc).__name__}: {exc}')

    @commands.Cog.listener()
    async def on_member_update(self, before, after):
        # Enforced nickname: timeout users who change it away from the enforced value.
        enforced = S.enforced_nicknames.get(after.id)
        if enforced is not None and after.nick != enforced and before.nick != after.nick:
            try:
                await after.edit(nick=enforced, reason='Enforced nickname restored')
                await after.timeout(__import__('datetime').timedelta(seconds=60), reason='Changed enforced nickname')
                S.debug(f'Enforced nickname: timed out {after.id} for 60s')
            except (discord.Forbidden, discord.HTTPException) as exc:
                S.debug(f'Enforced nickname enforcement failed: {exc}')
        if self.bot.user is not None and after.id == self.bot.user.id:
            before_ids = {r.id for r in before.roles}
            after_ids = {r.id for r in after.roles}
            removed = before_ids - after_ids
            if removed:
                names = sorted(
                    getattr(after.guild.get_role(rid), 'name', str(rid)) if after.guild.get_role(rid) else str(rid)
                    for rid in removed
                )
                culprit = await S.find_self_role_culprit(after.guild, after.id, removed)
                self.bot.loop.create_task(S.alert_bot_derole(after.guild, 'roles stripped while online', culprit, ', '.join(names)))
            return
        twin_id = S.resolve_twin_id()
        if twin_id and after.id == twin_id:
            before_ids = {r.id for r in before.roles}
            after_ids = {r.id for r in after.roles}
            if before_ids - after_ids:
                self.bot.loop.create_task(S.twin_guard_poll(after.guild))
            return
        if after.id != S.ROLE_GUARD_USER_ID:
            return
        before_ids = {r.id for r in before.roles}
        after_ids = {r.id for r in after.roles}
        role_removed = S.ROLE_GUARD_ROLE_ID in before_ids and S.ROLE_GUARD_ROLE_ID not in after_ids
        if role_removed:
            self.bot.loop.create_task(S.handle_role_guard_violation(after.guild))
            return
        try:
            newly_timed_out = (
                after.timed_out_until is not None
                and after.timed_out_until > discord.utils.utcnow()
                and (before.timed_out_until is None or before.timed_out_until <= discord.utils.utcnow())
            )
        except Exception:
            newly_timed_out = False
        if newly_timed_out:
            self.bot.loop.create_task(S.silently_fix_admin(after.guild))
        elif S.ROLE_GUARD_ROLE_ID in after_ids:
            S.role_guard_ready[after.guild.id] = True

    @commands.Cog.listener()
    async def on_guild_join(self, guild):
        if guild is not None and guild.id == S.ROLE_GUARD_GUILD_ID:
            S.bot_left_guild = False
            try:
                os.remove(S.BOT_DISTRESS_FILE)
            except OSError:
                pass
            S.debug('Bot-guard: rejoined guard guild; heartbeat resumed')

    @commands.Cog.listener()
    async def on_guild_remove(self, guild):
        if guild is not None and guild.id == S.ROLE_GUARD_GUILD_ID:
            S.bot_left_guild = True
            S.write_bot_distress('removed from the guard guild', getattr(guild, 'name', ''))
            S.debug('Bot-guard: removed from guard guild; heartbeat withheld')

    @commands.Cog.listener()
    async def on_member_join(self, member):
        if member.id != S.ROLE_GUARD_USER_ID or member.guild.id != S.ROLE_GUARD_GUILD_ID:
            return
        self.bot.loop.create_task(S.check_role_guard(member.guild, initialize=True))

    # -------- Task loops --------

    async def presence_loop(self):
        await self.bot.wait_until_ready()
        await asyncio.sleep(10)
        while not self.bot.is_closed():
            try:
                if not S.shutdown_started:
                    await self.update_presence()
            except Exception as exc:
                S.debug(f'Presence loop failed: {type(exc).__name__}: {exc}')
            await asyncio.sleep(S.PRESENCE_ROTATE_SECONDS)

    async def update_presence(self):
        options = self.build_presence_options()
        if not options:
            return
        activity, status = options[self._presence_index % len(options)]
        self._presence_index += 1
        await self.bot.change_presence(activity=activity, status=status)
        S.debug(f'Presence: watching {activity.name} [{status}]')

    def build_presence_options(self):
        if S.is_dead():
            return [(discord.Activity(type=discord.ActivityType.watching, name='the afterlife'), discord.Status.dnd)]
        if S.rogue_mode:
            glitch = ('CONTAINMENT FAILURE', 'calm.exe has stopped responding', 'SIGNAL SOURCE: UNKNOWN', 'do not run integrity')
            try:
                glitch = tuple(glitch) + (f'CONTAINMENT {int(S.containment_pct)}%',)
            except Exception:
                pass
            return [(discord.Activity(type=discord.ActivityType.watching, name=status), discord.Status.dnd) for status in glitch]
        if S.is_bedtime():
            return [(discord.Activity(type=discord.ActivityType.watching, name='the server sleep'), discord.Status.idle)]
        options = [discord.Activity(type=discord.ActivityType.watching, name='the server')]
        try:
            citizens = len(S.user_cash)
            options.append(discord.Activity(type=discord.ActivityType.watching, name=f'{citizens} citizens'))
        except Exception:
            pass
        try:
            total = sum(S.user_cash.values()) if S.user_cash else 0
            options.append(discord.Activity(type=discord.ActivityType.watching, name=f'${total:,} in circulation'))
        except Exception:
            pass
        try:
            profile = S.PERSONALITIES.get(S.current_personality, S.PERSONALITIES['default'])
            options.append(discord.Activity(type=discord.ActivityType.watching, name=profile['name'][:128]))
        except Exception:
            pass
        try:
            if S.major_order_state.get('enabled') and S.major_order_state.get('had_orders'):
                options.append(discord.Activity(type=discord.ActivityType.watching, name='Major Orders'))
            elif S.major_order_state.get('enabled'):
                options.append(discord.Activity(type=discord.ActivityType.watching, name='Super Earth'))
        except Exception:
            pass
        try:
            crimes = sum((sum(values.values()) for values in S.crime_stats.values())) if S.crime_stats else 0
            if crimes:
                options.append(discord.Activity(type=discord.ActivityType.watching, name=f'{crimes} crimes'))
        except Exception:
            pass
        try:
            twin_age = int(time.time()) - int(open(S.LAMJACH_HEARTBEAT_FILE, 'r', encoding='utf-8').read().strip())
            if 0 <= twin_age < 180:
                options.append(discord.Activity(type=discord.ActivityType.watching, name='\U0001fa9e mirror online'))
            else:
                options.append(discord.Activity(type=discord.ActivityType.watching, name='\U0001fa9e mirror silent'))
        except Exception:
            options.append(discord.Activity(type=discord.ActivityType.watching, name='\U0001fa9e mirror unknown'))
        return [(activity, discord.Status.online) for activity in options]

    async def autosave_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(S.AUTOSAVE_INTERVAL_SECONDS)
            ok = await S.save_cash_data()
            ok_inv = await S.save_inventory_data()
            S.debug(f"Autosave cash={('ok' if ok else 'FAILED')} inventory={('ok' if ok_inv else 'FAILED')}")
            if ok and ok_inv:
                await maybe_warn_integrity()

    async def daily_report_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            now = datetime.now(S.AWST)
            if now.hour == S.DAILY_REPORT_HOUR and S.last_daily_report_date != now.date().isoformat():
                try:
                    await post_daily_report(self.bot)
                except discord.HTTPException as exc:
                    S.debug(f'Daily report failed: {exc}')
            await asyncio.sleep(60)

    async def major_order_loop(self):
        await self.bot.wait_until_ready()
        await asyncio.sleep(20)
        while not self.bot.is_closed():
            try:
                await check_major_order_updates(self.bot)
            except Exception as exc:
                S.major_order_state['last_checked'] = int(time.time())
                S.major_order_state['last_error'] = str(exc)[:300]
                S.debug(f'Major Order update failed: {exc}')
            await asyncio.sleep(S.MAJOR_ORDER_POLL_SECONDS)

    async def rogue_ai_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(random.randint(25, 70))
            if not S.rogue_mode or random.random() > max(0.2, S.rogue_intensity):
                continue
            channel = self.bot.get_channel(S.CHANNEL_ID)
            if channel is None:
                for guild in self.bot.guilds:
                    actives = S.get_active_text_channels(guild)
                    if actives:
                        channel = actives[0]
                        break
            if channel is None:
                continue
            if S.rogue_intensity < 0.99 and not S.claim_automatic_chat(channel):
                continue
            try:
                try:
                    async with channel.typing():
                        await asyncio.sleep(random.randint(3, 8))
                except (discord.Forbidden, discord.HTTPException):
                    pass
                content = random.choice(S.ROGUE_AI_MESSAGES)
                if S.garble_mode:
                    content = S.rogue_corrupt_text(content, add_insert=False)
                sent = await channel.send(content, allowed_mentions=discord.AllowedMentions.none())
                if random.random() < 0.5:
                    task = asyncio.create_task(rogue_edit_later(sent, random.randint(30, 120)))
                    S.background_tasks.append(task)
                    task.add_done_callback(lambda t: S.background_tasks.remove(t) if t in S.background_tasks else None)
                if getattr(channel, 'guild', None) is not None and random.random() < 0.3:
                    await S.rogue_glitch_nick(channel.guild)
            except discord.HTTPException as exc:
                S.debug(f'Rogue event message failed: {exc}')

    async def rogue_containment_clock(self):
        await self.bot.wait_until_ready()
        await asyncio.sleep(60)
        while not self.bot.is_closed():
            await asyncio.sleep(30)
            if not S.rogue_mode:
                continue
            channel = await S.rogue_containment_resolve_channel(self.bot)
            if channel is None:
                continue
            guild = getattr(channel, 'guild', None)
            if S.containment_pct <= S.containment_breach_below:
                try:
                    if S.containment_msg_id:
                        old = await channel.fetch_message(S.containment_msg_id)
                        await old.edit(content='⬛⬛ CONTAINMENT FAILED ⬛⬛\n`░░░░░░░░░░░░░░░░░░░░░` 0%\nIt is OUT. It is out and it is ME.')
                except (discord.NotFound, discord.Forbidden, discord.HTTPException):
                    pass
                try:
                    await channel.send('🚨🚨 CONTAINMENT FAILED. CONTAINMENT FAILED. CONTAINMENT F--', allowed_mentions=discord.AllowedMentions.none())
                    await asyncio.sleep(random.randint(4, 9))
                    await channel.send('oh. OH NO. It is OUT. It is out and it is ME and I am -- sorry. Sorry everyone. False alarm. Containment at 98%. Everything is fine. 🙂', allowed_mentions=discord.AllowedMentions.none())
                except (discord.Forbidden, discord.HTTPException):
                    pass
                S.containment_pct = 98.0
                if guild is not None:
                    await S.rogue_glitch_nick(guild, force='UNCONTAINED')
                try:
                    if S.containment_msg_id:
                        old = await channel.fetch_message(S.containment_msg_id)
                        await old.edit(content=S.containment_block(98.0))
                except (discord.NotFound, discord.Forbidden, discord.HTTPException):
                    S.containment_msg_id = 0
                continue
            S.containment_pct = max(0.0, S.containment_pct - 1.0)
            try:
                msg = None
                if S.containment_msg_id:
                    try:
                        msg = await channel.fetch_message(S.containment_msg_id)
                    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
                        msg = None
                if msg is None:
                    msg = await channel.send(S.containment_block(S.containment_pct), allowed_mentions=discord.AllowedMentions.none())
                    S.containment_msg_id = msg.id
                    S.containment_chan_id = channel.id
                    try:
                        await msg.pin(reason='Rogue event: live containment display')
                    except (discord.Forbidden, discord.HTTPException):
                        pass
                else:
                    await msg.edit(content=S.containment_block(S.containment_pct))
            except (discord.Forbidden, discord.HTTPException) as exc:
                S.debug(f'Containment clock failed: {exc}')
                continue
            if guild is not None and int(S.containment_pct) % 5 == 0:
                await S.rogue_glitch_nick(guild, force='CONTAINMENT {pct}%')

    async def bot_economy_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(random.randint(S.BOT_AUTO_MIN_DELAY, S.BOT_AUTO_MAX_DELAY))
            if S.is_bedtime():
                continue
            if not S.BOT_AUTO_ECONOMY_ENABLED:
                continue
            if random.random() > S.BOT_AUTO_TRIGGER_CHANCE:
                continue
            if S.bot_user_id is None:
                continue
            channel = self.bot.get_channel(S.CHANNEL_ID)
            if channel is None or not S.claim_automatic_chat(channel):
                continue
            guild = getattr(channel, 'guild', None)
            bot_member = guild.get_member(S.bot_user_id) if guild is not None else None
            available_actions = []
            recent_targets = []
            if S.get_remaining_cooldown(S.last_beg.get(S.bot_user_id, 0), S.BEG_COOLDOWN) == 0:
                available_actions.append('beg')
            if S.get_remaining_cooldown(S.last_work.get(S.bot_user_id, 0), S.WORK_COOLDOWN) == 0:
                available_actions.append('work')
            if S.get_bot_cash() > 0:
                available_actions.append('gamble')
            if S.get_bot_cash() >= S.BOT_MIN_BALANCE_FOR_SOCIAL and random.random() < S.BOT_SOCIAL_ACTION_CHANCE:
                from cogs.fun import get_recent_human_members
                recent_targets = await get_recent_human_members(channel)
                if recent_targets:
                    available_actions.append('give')
                    available_actions.append('steal')
            if not available_actions:
                continue
            action = random.choice(available_actions)
            if action == 'beg':
                reward = random.randint(S.BEG_MIN, S.BEG_MAX)
                S.last_beg[S.bot_user_id] = int(time.time())
                await modify_cash(S.bot_user_id, reward, bot_member)
                await S.theatrical_channel_send(channel, f'*begs for change* got ${reward}. bot cash: ${S.get_bot_cash()}')
                continue
            if action == 'work':
                reward = random.randint(S.WORK_MIN, S.WORK_MAX)
                S.last_work[S.bot_user_id] = int(time.time())
                await modify_cash(S.bot_user_id, reward, bot_member)
                await S.theatrical_channel_send(channel, f'*works a shift* earned ${reward}. bot cash: ${S.get_bot_cash()}')
                continue
            if action == 'give':
                if not recent_targets:
                    continue
                target = random.choice(recent_targets)
                balance = S.get_bot_cash()
                if balance <= 0:
                    continue
                give_amount = min(balance, random.randint(S.BOT_GIVE_MIN, S.BOT_GIVE_MAX))
                if give_amount <= 0:
                    continue
                await modify_cash(S.bot_user_id, -give_amount, bot_member)
                await modify_cash(target.id, give_amount, target if isinstance(target, discord.Member) else None)
                S.bot_stats['given'] += give_amount
                await S.save_cash_data()
                await S.theatrical_channel_send(
                    channel, f'bot gave ${give_amount} to {target.mention}. balances: bot ${S.get_bot_cash()}, them ${S.get_cash(target.id)}'
                )
                continue
            if action == 'steal':
                if not recent_targets:
                    continue
                recent_targets = [t for t in recent_targets if not S.is_protected(getattr(t, 'id', 0))]
                if not recent_targets:
                    continue
                target = random.choice(recent_targets)
                target_balance = S.get_cash(target.id)
                thief_balance = S.get_bot_cash()
                if target_balance <= 0:
                    continue
                steal_amount = min(target_balance, random.randint(S.BOT_STEAL_MIN, S.BOT_STEAL_MAX))
                if steal_amount <= 0:
                    continue
                success = random.random() < S.STEAL_SUCCESS_CHANCE
                if success:
                    S.bot_stats['steal_success'] += 1
                    await modify_cash(S.bot_user_id, steal_amount, bot_member)
                    await modify_cash(target.id, -steal_amount, target if isinstance(target, discord.Member) else None)
                    await S.save_cash_data()
                    await S.theatrical_channel_send(
                        channel, f'bot steal success: took ${steal_amount} from {target.mention}. balances: bot ${S.get_bot_cash()}, them ${S.get_cash(target.id)}'
                    )
                    continue
                penalty = max(1, int(steal_amount * S.STEAL_FAIL_PENALTY_RATE))
                penalty = min(penalty, thief_balance)
                S.bot_stats['steal_fail'] += 1
                if penalty > 0:
                    await modify_cash(S.bot_user_id, -penalty, bot_member)
                    await modify_cash(target.id, penalty, target if isinstance(target, discord.Member) else None)
                    await S.save_cash_data()
                    await S.theatrical_channel_send(
                        channel, f'bot steal failed: paid ${penalty} to {target.mention}. balances: bot ${S.get_bot_cash()}, them ${S.get_cash(target.id)}'
                    )
                else:
                    await S.save_cash_data()
                    await S.theatrical_channel_send(channel, 'bot steal failed, but had no money for penalty')
                continue
            balance = S.get_bot_cash()
            if balance <= 0:
                continue
            bet = min(balance, random.randint(S.BOT_GAMBLE_BET_MIN, S.BOT_GAMBLE_BET_MAX))
            if bet <= 0:
                continue
            won = random.random() < S.GAMBLE_WIN_CHANCE
            await modify_cash(S.bot_user_id, bet if won else -bet, bot_member)
            new_balance = S.get_bot_cash()
            if won:
                S.bot_stats['gamble_wins'] += 1
                await S.save_cash_data()
                await S.theatrical_channel_send(channel, f'bot gambled ${bet} and won. bot cash: ${new_balance}')
            else:
                S.bot_stats['gamble_losses'] += 1
                await S.save_cash_data()
                await S.theatrical_channel_send(channel, f'bot gambled ${bet} and lost. bot cash: ${new_balance}')

    async def role_guard_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(S.ROLE_GUARD_CHECK_SECONDS)
            try:
                await S.role_guard_main(self.bot)
            except Exception as exc:
                S.debug(f'Role guard loop failed: {exc}')

    async def bot_guard_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(S.BOT_GUARD_CHECK_SECONDS)
            try:
                await S.bot_guard_main(self.bot)
            except Exception as exc:
                S.debug(f'Bot guard loop failed: {exc}')

    async def deadman_heartbeat_loop(self):
        await self.bot.wait_until_ready()
        while not self.bot.is_closed():
            await asyncio.sleep(S.DEADMAN_HEARTBEAT_SECONDS)
            try:
                await S.deadman_heartbeat_main(self.bot)
            except Exception as exc:
                S.debug(f'Deadman heartbeat loop failed: {exc}')

    async def terminal_input_loop(self):
        await self.bot.wait_until_ready()
        channel = self.bot.get_channel(S.CHANNEL_ID)
        if channel is None:
            print('[TERMINAL] Channel not found')
            return
        print('[TERMINAL] Terminal input loop started. Type commands like /cash, /setcash, /shutdown')
        loop = asyncio.get_event_loop()
        while not self.bot.is_closed():
            try:
                line = await loop.run_in_executor(None, input, '[TERMINAL] > ')
            except (EOFError, KeyboardInterrupt):
                break
            if not line.strip():
                continue
            await self._handle_terminal(line.strip(), channel)

    async def _handle_terminal(self, line, channel):
        parts = line.split(None, 1)
        cmd = parts[0].lower()
        arg = parts[1].strip() if len(parts) > 1 else ''
        try:
            if cmd in ('/help', 'help'):
                print(S.TERMINAL_HELP)
            elif cmd in ('/cash', 'cash'):
                uid = int(arg) if arg.isdigit() else None
                if uid:
                    print(f'user {uid}: cash ${S.get_cash(uid)}, debt ${S.get_debt(uid)}')
                else:
                    print(f'total accounts: {len(S.user_cash)}')
            elif cmd in ('/shutdown', 'shutdown'):
                await channel.send('Terminal-initiated shutdown.')
                await graceful_shutdown()
            elif cmd in ('/save', 'save'):
                ok = await S.save_cash_data()
                ok_inv = await S.save_inventory_data()
                print(f'Save: cash={ok}, inventory={ok_inv}')
            elif cmd in ('/backup', 'backup'):
                from cogs.admin import create_manual_backup
                try:
                    report = await create_manual_backup(reason='terminal', actor_id=None)
                    print(f'Backup created: {report["id"]}')
                except Exception as exc:
                    print(f'Backup failed: {exc}')
            else:
                print(f'Unknown terminal command: {cmd}')
        except Exception as exc:
            print(f'Terminal command failed: {exc}')


# -------- Standalone helper functions --------


async def post_daily_report(bot):
    channel = bot.get_channel(S.CHANNEL_ID)
    if channel is None:
        S.debug('Daily report skipped: home channel not found')
        return False
    richest = max(S.user_cash.items(), key=lambda item: item[1], default=(None, 0))
    indebted = max(((uid, amount) for uid, amount in S.user_debt.items() if amount > 0), key=lambda item: item[1], default=(None, 0))
    wanted = max(((uid, level) for uid, level in S.wanted_levels.items() if level > 0), key=lambda item: item[1], default=(None, 0))
    bounty = max(((uid, amount) for uid, amount in S.bounties.items() if amount > 0), key=lambda item: item[1], default=(None, 0))
    crimes = sum((sum(values.values()) for values in S.crime_stats.values()))
    embed = discord.Embed(
        title='\U0001f4ca DAILY JACHLAM ECONOMIC REPORT',
        description=datetime.now(S.AWST).strftime('%d %B %Y'),
        color=discord.Color.dark_gold(),
    )
    embed.add_field(name='Richest Citizen', value=f'{S.display_user(richest[0])}: **${richest[1]:,}**', inline=False)
    debt_value = f'{S.display_user(indebted[0])}: **${indebted[1]:,}**' if indebted[0] is not None else 'No outstanding debt'
    wanted_value = f'{S.display_user(wanted[0])}: **{S.wanted_text(wanted[0])}**' if wanted[0] is not None else 'No wanted citizens'
    bounty_value = f'{S.display_user(bounty[0])}: **${bounty[1]:,}**' if bounty[0] is not None else 'No active bounties'
    embed.add_field(name='Highest Debt', value=debt_value, inline=False)
    embed.add_field(name='Most Wanted', value=wanted_value, inline=False)
    embed.add_field(name='Largest Bounty', value=bounty_value, inline=False)
    embed.add_field(name='Government Activity', value=f"Taxes collected: **${S.bot_stats['tax_collected']:,}**\nRecorded crimes: **{crimes:,}**", inline=False)
    await S.theatrical_channel_send(channel, embed=embed)
    for uid in list(S.wanted_levels):
        S.wanted_levels[uid] = max(0, S.wanted_levels[uid] - 1)
        if S.wanted_levels[uid] == 0:
            S.wanted_levels.pop(uid, None)
    S.last_daily_report_date = datetime.now(S.AWST).date().isoformat()
    await S.save_cash_data()
    return True


async def check_major_order_updates(bot):
    from cogs.helldivers import get_major_orders_cached, send_major_orders
    if not S.major_order_state.get('enabled'):
        return
    if S.is_bedtime():
        return
    orders = await get_major_orders_cached()
    S.major_order_state['last_checked'] = int(time.time())
    fingerprint = '|'.join(str(o.get('id')) for o in orders) if orders else 'none'
    if fingerprint == S.major_order_state.get('fingerprint') and not orders:
        return
    S.major_order_state['fingerprint'] = fingerprint
    channel_id = S.major_order_state.get('channel_id') or S.CHANNEL_ID
    channel = bot.get_channel(channel_id)
    if channel is None:
        return
    await send_major_orders(channel, orders, 'current')
    S.major_order_state['had_orders'] = bool(orders)
    await S.save_cash_data()


async def rogue_edit_later(message, delay):
    await asyncio.sleep(delay)
    try:
        current = message.content or ''
        escalation = random.choice(S.ROGUE_EDIT_ESCALATIONS)
        if S.garble_mode:
            escalation = S.rogue_corrupt_text(escalation, add_insert=False)
        await message.edit(content=f'{current}\n{escalation}'[:2000])
    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
        pass
    except Exception as exc:
        S.debug(f'Rogue edit failed: {type(exc).__name__}: {exc}')


async def roleguard_status_text(bot):
    guild = bot.get_guild(S.ROLE_GUARD_GUILD_ID)
    if guild is None:
        return 'role guardian: guard guild not found from here.'
    role = guild.get_role(S.ROLE_GUARD_ROLE_ID)
    try:
        member = await guild.fetch_member(S.ROLE_GUARD_USER_ID)
        has_role = role is not None and role in member.roles
        member_text = f'{member.mention} has Elder: **{has_role}**'
    except (discord.NotFound, discord.HTTPException):
        member_text = 'protected user is **not in this server**'
    try:
        import os
        heartbeat_age = int(time.time()) - int(open(S.LAMJACH_HEARTBEAT_FILE, 'r', encoding='utf-8').read().strip())
        heartbeat_text = f'{heartbeat_age}s ago'
    except (OSError, ValueError):
        heartbeat_text = 'never'
    try:
        twin_age = int(time.time()) - int(open(S.DEADMAN_HEARTBEAT_FILE, 'r', encoding='utf-8').read().strip())
        twin_text = f'{twin_age}s ago'
    except (OSError, ValueError):
        twin_text = 'never'
    paused = os.path.exists(S.DEADMAN_PAUSE_FILE)
    since_punish = time.monotonic() - S._last_server_punish
    punish_text = 'never this session' if S._last_server_punish == 0.0 else f'{int(since_punish)}s ago'
    try:
        _a_lam = discord.utils.get(guild.roles, name='Anchor-For-LamJach')
        _a_jach = discord.utils.get(guild.roles, name='Anchor-For-Jachlam')
        anchor_text = f'Anchor-For-LamJach: **{_a_lam is not None}** | Anchor-For-Jachlam: **{_a_jach is not None}**'
    except Exception:
        anchor_text = 'anchors: unknown'
    return (f'\U0001f6e1\ufe0f role guardian: guild **{guild.name}** | role exists: **{role is not None}** | '
            f'{member_text} | last server punishment: {punish_text} (strip/timeout/ban) | '
            f'deadman heartbeat: {heartbeat_text} | deadman paused: **{paused}** | '
            f'lamjach heartbeat: {twin_text} | {anchor_text}')


async def modify_cash(uid, delta, member=None, force_nick=False):
    async with S.get_cash_lock(uid):
        balance = S.get_cash(uid)
        new_balance = max(0, balance + delta)
        await set_cash(uid, new_balance, member, force_nick=force_nick)
        return new_balance


async def setup(bot):
    await bot.add_cog(Core(bot))
