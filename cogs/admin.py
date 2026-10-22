"""Jachlam Admin Cog — prefix admin commands (no slash slots used).

Includes economy/system/moderation admin commands, plus backup, integrity,
debug, shutdown, and personality controls. All commands are manual `!`-prefix
parsing on on_message to stay under Discord's ~100 global slash-command cap.
"""

import re
import time
import discord
from discord.ext import commands
from datetime import timedelta

from cogs import state as S
from cogs.core import rogue_send, post_daily_report
from cogs.moderation import find_shop_item

class Admin(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @commands.hybrid_command(name='changelog', description='Read Jachlam update history.')
    async def changelog(self, ctx, page: int = 1):
        if not S.is_active_channel(ctx.channel):
            return
        total_pages = len(S.CHANGELOG_PAGES)
        if not 1 <= page <= total_pages:
            await rogue_send(ctx, f'choose a changelog page from `1` to `{total_pages}`.')
            return
        entry = S.CHANGELOG_PAGES[page - 1]
        embed = discord.Embed(title=f"\U0001f4dc Jachlam Changelog - {entry['date']}", description=f"## {entry['title']}", color=discord.Color.gold())
        embed.add_field(name='Changes', value='\n'.join((f'\u2022 {change}' for change in entry['changes'])), inline=False)
        if entry.get('url'):
            embed.add_field(name='GitHub', value=f"[View changes on GitHub]({entry.get('url')})", inline=False)
        embed.set_footer(text=f'Page {page}/{total_pages}')
        await rogue_send(ctx, embed=embed)

    async def _prefix_reply(self, message, text=None, embed=None):
        try:
            await message.channel.send(text if embed is None else None, embed=embed)
        except (discord.Forbidden, discord.HTTPException) as exc:
            S.debug(f'prefix admin reply failed: {exc}')

    async def check_prefix_admin_commands(self, message):
        """Manual `!` admin dispatcher. Returns True if the message was handled."""
        author = getattr(message, 'author', None)
        if author is None or getattr(author, 'bot', False):
            return False
        content = (message.content or '').strip()
        if not content.startswith('!'):
            return False
        parts = content[1:].split(None, 1)
        name = parts[0].lower() if parts else ''
        arg = parts[1].strip() if len(parts) > 1 else ''
        if name not in S.PREFIX_ADMIN_COMMANDS:
            return False
        guild = message.guild
        if guild is None:
            await self._prefix_reply(message, 'prefix admin commands only work in a server.')
            return True
        if name == 'adminhelp':
            lines = ['**! admin commands** (no slash slots used):']
            for cmd in sorted(S.PREFIX_ADMIN_COMMANDS):
                lines.append(f'`!{cmd}` - {S.PREFIX_ADMIN_COMMANDS[cmd]}')
            lines.append('economy/system/moderation commands require admin or the matching Discord permission.')
            await self._prefix_reply(message, '\n'.join(lines)[:1900])
            return True
        channel = message.channel

        # -------- Economy/system admin --------
        if name in ('setcash', 'addcash', 'takecash', 'setdebt', 'adddebt', 'takedebt', 'resetuser', 'setbotcash'):
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            if name == 'setbotcash':
                amount = S._prefix_parse_amount(arg)
                if amount is None or amount < 0:
                    await self._prefix_reply(message, 'usage: `!setbotcash <amount>`')
                    return True
                if S.bot_user_id is None:
                    await self._prefix_reply(message, 'bot cash is not ready yet')
                    return True
                await S.set_cash_locked(S.bot_user_id, amount, guild.get_member(S.bot_user_id), force_nick=True)
                await self._prefix_reply(message, f'set bot cash to ${S.get_bot_cash()}')
                return True
            target, amount, err = S._prefix_split_member_amount(guild, arg)
            if err:
                await self._prefix_reply(message, f'{err} usage: `!{name} @user <amount>`' if name != 'resetuser' else 'usage: `!resetuser @user`')
                return True
            member = target if isinstance(target, discord.Member) else guild.get_member(int(target))
            mention = member.mention if isinstance(member, discord.Member) else f'<@{int(target)}>'
            tid = target.id if isinstance(target, discord.Member) else int(target)
            if name == 'resetuser':
                if S.is_protected(tid):
                    await self._prefix_reply(message, f'{mention} is protected and cannot be reset.')
                    return True
                S.clear_user_state(tid)
                if isinstance(member, discord.Member):
                    from cogs.core import update_cash_nick
                    await update_cash_nick(member, S.STARTING_CASH, force=True)
                await S.save_cash_data()
                await self._prefix_reply(message, f'reset {mention}: cash ${S.STARTING_CASH}, debt $0, and all cooldowns cleared')
                return True
            if amount is None or (amount <= 0 and name in ('addcash', 'takecash', 'adddebt', 'takedebt')) or (amount < 0 and name in ('setcash', 'setdebt')):
                await self._prefix_reply(message, 'amount must be more than 0')
                return True
            if name == 'setcash':
                if S.is_protected(tid) and amount < S.get_cash(tid):
                    await self._prefix_reply(message, f'{mention} is protected and their cash cannot be lowered.')
                    return True
                await S.set_cash_locked(tid, amount, member, force_nick=True)
                await self._prefix_reply(message, f'set {mention} cash to ${S.get_cash(tid)}')
            elif name == 'addcash':
                from cogs.core import modify_cash
                await modify_cash(tid, amount, member, force_nick=True)
                await self._prefix_reply(message, f'added ${amount} to {mention}. new cash: ${S.get_cash(tid)}')
            elif name == 'takecash':
                if S.is_protected(tid):
                    await self._prefix_reply(message, f'{mention} is protected and their cash cannot be taken.')
                    return True
                from cogs.core import modify_cash
                await modify_cash(tid, -amount, member, force_nick=True)
                await self._prefix_reply(message, f'took ${amount} from {mention}. new cash: ${S.get_cash(tid)}')
            elif name == 'setdebt':
                if S.is_protected(tid) and amount > 0:
                    await self._prefix_reply(message, f'{mention} is protected and cannot be given debt.')
                    return True
                S.user_debt[tid] = max(0, amount)
                if S.user_debt[tid] == 0:
                    S.last_debt_penalty.pop(tid, None)
                else:
                    S.last_debt_penalty[tid] = int(time.time())
                await S.save_cash_data()
                await self._prefix_reply(message, f'set {mention} debt to ${S.get_debt(tid)}')
            elif name == 'adddebt':
                if S.is_protected(tid):
                    await self._prefix_reply(message, f'{mention} is protected and cannot be given debt.')
                    return True
                S.user_debt[tid] = S.get_debt(tid) + amount
                S.last_debt_penalty[tid] = int(time.time())
                await S.save_cash_data()
                await self._prefix_reply(message, f'added ${amount} debt to {mention}. new debt: ${S.get_debt(tid)}')
            elif name == 'takedebt':
                S.user_debt[tid] = max(0, S.get_debt(tid) - amount)
                if S.user_debt[tid] == 0:
                    S.last_debt_penalty.pop(tid, None)
                await S.save_cash_data()
                await self._prefix_reply(message, f'took ${amount} debt from {mention}. new debt: ${S.get_debt(tid)}')
            return True

        if name == 'giveitem':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split()
            if len(tokens) < 2:
                await self._prefix_reply(message, 'usage: `!giveitem @user <item> [qty]`')
                return True
            target = S.resolve_epstein_target(guild, tokens[0]) or S.resolve_epstein_target(guild, tokens[-1])
            if target is None:
                await self._prefix_reply(message, 'could not find that member (mention or user ID).')
                return True
            tid = target.id if isinstance(target, discord.Member) else int(target)
            qty = 1
            item_query = ' '.join(tokens[1:])
            last_tok = tokens[-1]
            maybe_qty = S._prefix_parse_amount(last_tok)
            first_is_member = S.resolve_epstein_target(guild, tokens[0]) is not None
            if first_is_member and maybe_qty is not None and len(tokens) >= 3:
                qty = maybe_qty
                item_query = ' '.join(tokens[1:-1])
            elif not first_is_member:
                item_query = ' '.join(tokens[:-1])
            if qty <= 0:
                await self._prefix_reply(message, 'quantity must be more than 0')
                return True
            item_id = find_shop_item(item_query)
            if item_id is None:
                await self._prefix_reply(message, f"no item called '{item_query[:80]}'")
                return True
            S.add_item(tid, item_id, qty)
            await S.save_inventory_data()
            mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
            await self._prefix_reply(message, f"gave {qty}x **{S.SHOP_ITEMS[item_id]['name']}** to {mention}")
            return True

        if name == 'clearcooldowns':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            target = S.resolve_epstein_target(guild, arg)
            if target is None:
                await self._prefix_reply(message, 'usage: `!clearcooldowns @user`')
                return True
            tid = target.id if isinstance(target, discord.Member) else int(target)
            for store in (S.last_beg, S.last_work, S.last_pray, S.last_loan, S.last_tax, S.last_dig, S.last_assassinate):
                store.pop(tid, None)
            mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
            await S.save_cash_data()
            await self._prefix_reply(message, f'cleared all command cooldowns for {mention}.')
            return True

        if name == 'setwanted':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split()
            if len(tokens) < 2:
                await self._prefix_reply(message, 'usage: `!setwanted @user 0-5`')
                return True
            target = S.resolve_epstein_target(guild, ' '.join(tokens[:-1])) or S.resolve_epstein_target(guild, tokens[0])
            level = S._prefix_parse_amount(tokens[-1])
            if target is None or level is None or not 0 <= level <= S.MAX_WANTED_LEVEL:
                await self._prefix_reply(message, 'usage: `!setwanted @user 0-5`')
                return True
            tid = target.id if isinstance(target, discord.Member) else int(target)
            if S.is_protected(tid) and level > 0:
                mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
                await self._prefix_reply(message, f'{mention} is protected and cannot be wanted.')
                return True
            S.wanted_levels[tid] = level
            S.refresh_achievements(tid)
            await S.save_cash_data()
            mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
            await self._prefix_reply(message, f'set {mention} wanted level to **{S.wanted_text(tid)}**')
            return True

        if name == 'clearbounty':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            target = S.resolve_epstein_target(guild, arg)
            if target is None:
                await self._prefix_reply(message, 'usage: `!clearbounty @user`')
                return True
            tid = target.id if isinstance(target, discord.Member) else int(target)
            removed = S.bounties.pop(tid, 0)
            await S.save_cash_data()
            mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
            await self._prefix_reply(message, f'cleared {mention} bounty (was ${removed:,}).')
            return True

        if name == 'forcetaxall':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            total_collected = 0
            users_taxed = 0
            for uid in list(S.user_cash.keys()):
                S.last_tax[uid] = 0
                tax_amount, _rate = await S.apply_tax_if_due(uid, guild.get_member(uid))
                users_taxed += 1
                if tax_amount > 0:
                    total_collected += tax_amount
            await self._prefix_reply(message, f'forced tax on {users_taxed} users, collected ${total_collected}')
            return True

        if name in ('sleep', 'wake'):
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            if name == 'sleep':
                S.sleep_override = True
                S.bot_is_asleep = True
                await self._prefix_reply(message, 'going to bed, back at 7am' if S.is_bedtime() else 'fine... going to bed early i guess :(')
            else:
                S.sleep_override = None
                S.bot_is_asleep = False
                await self._prefix_reply(message, "morning, i'm awake")
            return True

        if name in ('rogue', 'garble'):
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            state = arg.split(None, 1)[0].lower() if arg else 'status'
            if name == 'rogue':
                if state == 'on':
                    rest = arg.split(None, 1)[1] if len(arg.split(None, 1)) > 1 else ''
                    if rest:
                        try:
                            percent = int(rest)
                        except ValueError:
                            await self._prefix_reply(message, 'intensity must be a number from 10 to 100')
                            return True
                        if percent < 10 or percent > 100:
                            await self._prefix_reply(message, 'intensity must be from 10 to 100')
                            return True
                        S.rogue_intensity = percent / 100
                    S.rogue_mode = True
                    await self._prefix_reply(message, f'ROGUE EVENT ARMED at {round(S.rogue_intensity * 100)}% intensity')
                elif state == 'off':
                    S.rogue_mode = False
                    await self._prefix_reply(message, 'ROGUE EVENT CONTAINED; outgoing presentation restored')
                elif state == 'status':
                    await self._prefix_reply(message, f"rogue event: {('ON' if S.rogue_mode else 'OFF')} | intensity {round(S.rogue_intensity * 100)}%")
                else:
                    await self._prefix_reply(message, 'usage: `!rogue on [10-100] | !rogue off | !rogue status`')
                return True
            if state == 'on':
                S.garble_mode = True
                await self._prefix_reply(message, 'garble ON: every ordinary bot response will be corrupted')
            elif state == 'off':
                S.garble_mode = False
                await self._prefix_reply(message, 'garble OFF')
            elif state == 'status':
                await self._prefix_reply(message, f"garble: {('ON' if S.garble_mode else 'OFF')}")
            else:
                await self._prefix_reply(message, 'usage: `!garble on | !garble off | !garble status`')
            return True

        if name == 'forcesave':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            await S.save_cash_data()
            await S.save_inventory_data()
            await S.save_seen_gif_keys()
            await self._prefix_reply(message, 'saved cash, inventory, and GIF memory.')
            return True

        if name == 'backup':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            reason = arg.strip()[:120] or 'manual admin backup (!backup)'
            try:
                report = await create_manual_backup(reason, author.id)
            except Exception as exc:
                S.debug(f'prefix backup failed: {exc}')
                await self._prefix_reply(message, 'backup failed. run `!integrity` and check the console.')
                return True
            await self._prefix_reply(message, f"backup `{report['id']}` created ({len(report['files'])} files validated). reason: {reason}")
            return True

        if name in ('backupstatus', 'integrity'):
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            report = collect_integrity_report()
            if name == 'backupstatus':
                cash = report['files'][S.CASH_FILE]
                inventory = report['files'][S.INVENTORY_FILE]
                lines = [
                    f"cash main: {_health_text(cash['main'])} | rolling: {_health_text(cash['rolling'])}",
                    f"inventory main: {_health_text(inventory['main'])} | rolling: {_health_text(inventory['rolling'])}",
                ]
                if report['latest'] is None:
                    lines.append('manual backups: none yet. run `!backup`.')
                else:
                    latest = report['latest']
                    lines.append(f"manual backups: **{len(report['backup_ids'])}** | latest `{latest['id']}` ({'valid' if latest['valid'] else 'INVALID'})")
                if report['alerts'] or report['issues']:
                    lines.append('warnings:\n' + '\n'.join(f'- {item}' for item in (report['alerts'] + report['issues'])[:8]))
                await self._prefix_reply(message, '\n'.join(lines)[:1900])
            else:
                if not report['alerts'] and not report['issues']:
                    await self._prefix_reply(message, 'integrity: all files valid, no warnings.')
                else:
                    await self._prefix_reply(message, ('integrity warnings:\n' + '\n'.join(f'- {item}' for item in (report['alerts'] + report['issues'])[:10]))[:1900])
            return True

        if name == 'debugstate':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            running = sum(1 for task in S.background_tasks if not task.done())
            await self._prefix_reply(message, f'`{S.JACHLAM_VERSION}` | uptime {S.fmt_seconds(int(time.monotonic() - S.bot_started_at))} | tasks running {running} | cash {len(S.user_cash)} | inv {len(S.user_inventory)} | mode {S.mode} | sleeping {S.bot_is_asleep} | wanted {sum(1 for v in S.wanted_levels.values() if v)} | bounties {sum(1 for v in S.bounties.values() if v)}')
            return True

        if name == 'debuguser':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            target = S.resolve_epstein_target(guild, arg) if arg else author
            if target is None:
                await self._prefix_reply(message, 'usage: `!debuguser [@user]`')
                return True
            tid = target.id if isinstance(target, discord.Member) else int(target)
            mention = target.mention if isinstance(target, discord.Member) else f'<@{tid}>'
            await self._prefix_reply(message, f'{mention} cash ${S.get_cash(tid):,} (shown ${S.get_display_cash(tid):,}) | debt ${S.get_debt(tid):,} | wanted {S.wanted_text(tid)} | bounty ${S.bounties.get(tid, 0):,} | crimes {sum(S.crime_stats.get(tid, {}).values())} | beg {S.fmt_seconds(S.get_remaining_cooldown(S.last_beg.get(tid, 0), S.BEG_COOLDOWN))} | work {S.fmt_seconds(S.get_remaining_cooldown(S.last_work.get(tid, 0), S.WORK_COOLDOWN))} | tax {S.fmt_seconds(S.get_remaining_cooldown(S.last_tax.get(tid, 0), S.TAX_INTERVAL_SECONDS))}')
            return True

        if name == 'recenterrors':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            limit = S._prefix_parse_amount(arg) if arg else 5
            limit = max(1, min(10, limit or 5))
            if not S.recent_errors:
                await self._prefix_reply(message, 'no unhandled command errors this session.')
                return True
            lines = [f"`{item['id']}` **{item['command']}** - {item['type']}: {item['message']}" for item in list(S.recent_errors)[-limit:][::-1]]
            await self._prefix_reply(message, '\n'.join(lines)[:1900])
            return True

        if name == 'dailyreport':
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            await post_daily_report(self.bot)
            return True

        if name == 'personality':
            if not arg:
                profile = S.PERSONALITIES.get(S.current_personality, S.PERSONALITIES['default'])
                await self._prefix_reply(message, f"current personality: **{profile['name']}** ({S.current_personality}). modes: {', '.join(sorted(S.PERSONALITIES))}")
                return True
            if not S._prefix_is_admin(author):
                await self._prefix_reply(message, 'not allowed')
                return True
            key = arg.strip().casefold()
            key = {'normal': 'default', 'off': 'default', 'government': 'bureaucrat', 'govt': 'bureaucrat',
                   'super earth': 'helldiver', 'goblin': 'gremlin', 'nice': 'wholesome', 'emo': 'existential',
                   'teen': 'angsty', 'angsty teen': 'angsty'}.get(key, key)
            if key not in S.PERSONALITIES:
                await self._prefix_reply(message, f"unknown mode. modes: {', '.join(sorted(S.PERSONALITIES))}")
                return True
            S.current_personality = key
            await S.save_cash_data()
            await self._prefix_reply(message, f"personality set to **{S.PERSONALITIES[key]['name']}**")
            return True

        # -------- Moderation admin --------
        if name == 'purge':
            if not S._prefix_has(author, 'manage_messages'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split()
            if not tokens:
                await self._prefix_reply(message, 'usage: `!purge <1-200> [confirm]`')
                return True
            amount = S._prefix_parse_amount(tokens[0])
            if amount is None or not 1 <= amount <= 200:
                await self._prefix_reply(message, 'choose between 1 and 200 messages.')
                return True
            if amount > 50 and (len(tokens) < 2 or tokens[1].casefold() != 'confirm'):
                await self._prefix_reply(message, f'this will delete **{amount}** messages. run `!purge {amount} confirm` to continue.')
                return True
            try:
                deleted = await channel.purge(limit=amount)
            except discord.Forbidden:
                await self._prefix_reply(message, 'Jachlam needs Manage Messages permission to purge here.')
                return True
            except discord.HTTPException as exc:
                S.debug(f'prefix purge failed: {exc}')
                await self._prefix_reply(message, 'the purge failed. check the server console.')
                return True
            await self._prefix_reply(message, f'deleted **{len(deleted)}** previous messages.')
            return True

        if name in ('timeout', 'untimeout'):
            if not S._prefix_has(author, 'moderate_members'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split()
            if not tokens:
                await self._prefix_reply(message, f'usage: `!{name} @user`' + (' <duration> [reason]' if name == 'timeout' else ''))
                return True
            target = S.resolve_epstein_target(guild, tokens[0])
            if target is None or not isinstance(target, discord.Member):
                await self._prefix_reply(message, 'member must be in this server (mention or user ID).')
                return True
            if S.is_protected(target.id):
                await self._prefix_reply(message, f'{target.mention} is protected and cannot be timed out.')
                return True
            try:
                if name == 'untimeout':
                    await target.remove_timeout(reason=f'untimeout by {author}')
                    await self._prefix_reply(message, f'removed timeout for {target.mention}.')
                else:
                    if len(tokens) < 2:
                        await self._prefix_reply(message, 'usage: `!timeout @user 10m [reason]` (try 10s/10m/2h/7d, max 28d; bare number = minutes)')
                        return True
                    seconds = S._prefix_parse_duration(tokens[1])
                    if seconds is None:
                        await self._prefix_reply(message, 'bad duration. try `10m`, `2h`, `7d` (max 28d).')
                        return True
                    reason = ' '.join(tokens[2:]).strip()[:300] or f'timeout by {author}'
                    await target.timeout(timedelta(seconds=seconds), reason=reason)
                    await self._prefix_reply(message, f'timed out {target.mention} for {S.fmt_seconds(seconds)}. reason: {reason}')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (check role position + Moderate Members).')
            except discord.HTTPException as exc:
                S.debug(f'prefix timeout failed: {exc}')
                await self._prefix_reply(message, 'timeout failed. check the server console.')
            return True

        if name == 'kick':
            if not S._prefix_has(author, 'kick_members'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split(None, 1)
            if not tokens:
                await self._prefix_reply(message, 'usage: `!kick @user [reason]`')
                return True
            target = S.resolve_epstein_target(guild, tokens[0].split(None, 1)[0] if tokens else '')
            if target is None:
                target = S.resolve_epstein_target(guild, arg)
            if target is None or not isinstance(target, discord.Member):
                await self._prefix_reply(message, 'member must be in this server (mention or user ID).')
                return True
            if S.is_protected(target.id):
                await self._prefix_reply(message, f'{target.mention} is protected and cannot be kicked.')
                return True
            reason = arg[len(tokens[0]):].strip()[:300] or f'kick by {author}'
            try:
                await target.kick(reason=reason)
                await self._prefix_reply(message, f'kicked {target.mention}. reason: {reason}')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (check role position + Kick Members).')
            except discord.HTTPException as exc:
                S.debug(f'prefix kick failed: {exc}')
                await self._prefix_reply(message, 'kick failed. check the server console.')
            return True

        if name in ('ban', 'unban'):
            if not S._prefix_has(author, 'ban_members'):
                await self._prefix_reply(message, 'not allowed')
                return True
            if name == 'unban':
                user_id = None
                m = re.search(r'\d{15,25}', arg)
                if m:
                    user_id = int(m.group(0))
                if user_id is None:
                    await self._prefix_reply(message, 'usage: `!unban <user_id>`')
                    return True
                try:
                    await guild.unban(discord.Object(id=user_id), reason=f'unban by {author}')
                    await self._prefix_reply(message, f'unbanned <@{user_id}>.')
                except discord.NotFound:
                    await self._prefix_reply(message, 'that user is not banned.')
                except discord.Forbidden:
                    await self._prefix_reply(message, 'no permission (check role position + Ban Members).')
                except discord.HTTPException as exc:
                    S.debug(f'prefix unban failed: {exc}')
                    await self._prefix_reply(message, 'unban failed. check the server console.')
                return True
            tokens = arg.split(None, 1)
            if not tokens:
                await self._prefix_reply(message, 'usage: `!ban @user [reason]`')
                return True
            target = S.resolve_epstein_target(guild, tokens[0])
            if target is None:
                target = S.resolve_epstein_target(guild, arg)
            if target is None or not isinstance(target, discord.Member):
                await self._prefix_reply(message, 'member must be in this server (mention or user ID).')
                return True
            if S.is_protected(target.id):
                await self._prefix_reply(message, f'{target.mention} is protected and cannot be banned.')
                return True
            reason = arg[len(tokens[0]):].strip()[:300] or f'ban by {author}'
            try:
                await target.ban(reason=reason, delete_message_days=0)
                await self._prefix_reply(message, f'banned {target.mention}. reason: {reason}')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (check role position + Ban Members).')
            except discord.HTTPException as exc:
                S.debug(f'prefix ban failed: {exc}')
                await self._prefix_reply(message, 'ban failed. check the server console.')
            return True

        if name == 'slowmode':
            if not S._prefix_has(author, 'manage_channels'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split()
            if not tokens:
                await self._prefix_reply(message, 'usage: `!slowmode <seconds 0-21600> [#channel]`')
                return True
            seconds = S._prefix_parse_amount(tokens[0])
            if seconds is None or not 0 <= seconds <= 21600:
                await self._prefix_reply(message, 'slowmode must be 0-21600 seconds (0 = off).')
                return True
            target_channel = channel
            if len(tokens) > 1:
                m = re.search(r'\d{15,25}', ' '.join(tokens[1:]))
                if m:
                    found = guild.get_channel(int(m.group(0)))
                    if isinstance(found, discord.TextChannel):
                        target_channel = found
            try:
                await target_channel.edit(slowmode_delay=seconds, reason=f'slowmode by {author}')
                await self._prefix_reply(message, f'slowmode in {target_channel.mention} set to {seconds}s.')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (Manage Channels).')
            except discord.HTTPException as exc:
                S.debug(f'prefix slowmode failed: {exc}')
                await self._prefix_reply(message, 'slowmode failed. check the server console.')
            return True

        if name in ('lock', 'unlock'):
            if not S._prefix_has(author, 'manage_channels'):
                await self._prefix_reply(message, 'not allowed')
                return True
            target_channel = channel
            m = re.search(r'\d{15,25}', arg)
            if m:
                found = guild.get_channel(int(m.group(0)))
                if isinstance(found, discord.TextChannel):
                    target_channel = found
            try:
                overwrite = target_channel.overwrites_for(guild.default_role)
                if name == 'lock':
                    overwrite.send_messages = False
                else:
                    overwrite.send_messages = None
                await target_channel.set_permissions(guild.default_role, overwrite=overwrite, reason=f'{name} by {author}')
                await self._prefix_reply(message, f'{target_channel.mention} {"locked" if name == "lock" else "unlocked"}.')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (Manage Channels).')
            except discord.HTTPException as exc:
                S.debug(f'prefix lock failed: {exc}')
                await self._prefix_reply(message, f'{name} failed. check the server console.')
            return True

        if name == 'nick':
            if not S._prefix_has(author, 'manage_nicknames'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split(None, 1)
            if not tokens:
                await self._prefix_reply(message, 'usage: `!nick @user New Name` (or `!nick @user none` to clear)')
                return True
            target = S.resolve_epstein_target(guild, tokens[0])
            rest = arg[len(tokens[0]):].strip() if target is not None else ''
            if target is None:
                await self._prefix_reply(message, 'usage: `!nick @user New Name`')
                return True
            if not isinstance(target, discord.Member):
                await self._prefix_reply(message, 'member must be in this server.')
                return True
            new_nick = None if rest.casefold() in ('none', 'clear', 'off') else rest[:32]
            if not new_nick:
                await self._prefix_reply(message, 'usage: `!nick @user New Name`')
                return True
            try:
                await target.edit(nick=new_nick, reason=f'nick by {author}')
                await self._prefix_reply(message, f'set nick for {target.mention} to **{new_nick}**.' if new_nick else f'cleared nick for {target.mention}.')
            except discord.Forbidden:
                await self._prefix_reply(message, 'no permission (check role position + Manage Nicknames).')
            except discord.HTTPException as exc:
                S.debug(f'prefix nick failed: {exc}')
                await self._prefix_reply(message, 'nick change failed. check the server console.')
            return True

        if name == 'forcenickname':
            if not S._prefix_has(author, 'manage_nicknames'):
                await self._prefix_reply(message, 'not allowed')
                return True
            tokens = arg.split(None, 1)
            if not tokens:
                await self._prefix_reply(message, 'usage: `!forcenickname @user <nickname>`')
                return True
            target = S.resolve_epstein_target(guild, tokens[0])
            if target is None or not isinstance(target, discord.Member):
                await self._prefix_reply(message, 'member must be in this server (mention or user ID).')
                return True
            if len(tokens) < 2:
                # clearing an enforced nickname
                S.enforced_nicknames.pop(target.id, None)
                await S.save_cash_data()
                await self._prefix_reply(message, f'enforced nickname cleared for {target.mention}.')
                return True
            new_nick = tokens[1].strip()[:32]
            if not new_nick:
                await self._prefix_reply(message, 'nickname must not be empty.')
                return True
            S.enforced_nicknames[target.id] = new_nick
            await S.save_cash_data()
            try:
                await target.edit(nick=new_nick, reason=f'Enforced nickname by {author}')
            except (discord.Forbidden, discord.HTTPException):
                pass
            await self._prefix_reply(message, f'enforced nickname for {target.mention} set to **{new_nick}**. changing it triggers a 60s timeout.')

        return False


def _health_text(info):
    return f"{info['status']} ({info.get('bytes', 0)} bytes)"


def collect_integrity_report():
    from cogs.state import collect_integrity_report as _f
    return _f()


async def create_manual_backup(reason, actor_id):
    from cogs.admin_backup import create_manual_backup as _f
    return await _f(reason, actor_id)


async def setup(bot):
    await bot.add_cog(Admin(bot))
