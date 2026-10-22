"""Jachlam Economy Cog — slash commands for cash, debt, tax, loans, gamble, beg, work, pray, steal, give."""

import random
import discord
from discord.ext import commands

from cogs import state as S
from cogs.core import set_cash, modify_cash, rogue_send
from cogs.state import debit_cash
from cogs.state import apply_tax_if_due, save_cash_data


class Economy(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @commands.hybrid_command(name='cash', description='Show your real cash balance and refresh your nickname.')
    async def cash_command(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        balance = S.get_cash(uid)
        member = ctx.author if isinstance(ctx.author, discord.Member) else None
        await set_cash(uid, balance, member, force_nick=True)
        await rogue_send(ctx, f'Your balance: **${balance:,}**')

    @commands.hybrid_command(name='leaderboard', description='Show the ten richest citizens.')
    async def leaderboard(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        ranked = sorted(S.user_cash.items(), key=lambda pair: pair[1], reverse=True)
        ranked = [(uid, amount) for uid, amount in ranked if uid != S.bot_user_id]
        if not ranked:
            await rogue_send(ctx, 'nobody has any cash yet')
            return
        lines = []
        medals = {0: '\U0001f947', 1: '\U0001f948', 2: '\U0001f949'}
        for i, (uid, amount) in enumerate(ranked[:10]):
            guild_member = ctx.guild.get_member(uid) if ctx.guild is not None else None
            name = guild_member.display_name if guild_member is not None else f'user {uid}'
            name = S._clean_display_name(name)
            rank_marker = medals.get(i, f'{i + 1}.')
            debt = S.get_debt(uid)
            debt_note = f' (debt ${debt})' if debt > 0 else ''
            lines.append(f'{rank_marker} **{name}** \u2014 ${S.get_display_cash(uid)}{debt_note}')
        embed = discord.Embed(title='cash leaderboard', description='\n'.join(lines), color=discord.Color.gold())
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='stats', description="Show a citizen's economy, protection, crime, and item stats.")
    async def stats(self, ctx, member: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        target = member or ctx.author
        uid = target.id
        inv_qty = sum(S.user_inventory.get(uid, {}).values())
        await rogue_send(ctx, (
            f'{target.mention}: cash ${S.get_cash(uid):,} (shown ${S.get_display_cash(uid):,}) | '
            f'debt ${S.get_debt(uid):,} | wanted {S.wanted_text(uid)} | bounty ${S.bounties.get(uid, 0):,} | '
            f'crimes {sum(S.crime_stats.get(uid, {}).values())} | items {inv_qty} | '
            f'charges {S.get_assassin_charges(uid)} | protection {S.get_protection_remaining(uid)}s'
        ))

    @commands.hybrid_command(name='gamble', description='Bet cash with the current gambling odds and active luck boosts.')
    async def gamble(self, ctx, amount: str):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        member = ctx.author
        if amount.lower() == 'all':
            bet = S.get_cash(uid)
        else:
            try:
                bet = int(amount.replace(',', '').replace('$', ''))
            except ValueError:
                await rogue_send(ctx, 'amount must be a number or `all`.')
                return
        if bet <= 0:
            await rogue_send(ctx, 'bet must be more than 0')
            return
        balance = S.get_cash(uid)
        if balance < bet:
            await rogue_send(ctx, f'you only have ${balance:,}. no bet was placed.')
            return
        win_chance = S.GAMBLE_WIN_CHANCE
        if S.has_luck_boost(uid):
            win_chance = min(0.99, win_chance + 0.35)
        won = random.random() < win_chance
        if won:
            await modify_cash(uid, bet, member)
            S.bot_stats['gamble_wins'] += 1
            await rogue_send(ctx, f'{member.mention} won **${bet:,}**! balance: ${S.get_cash(uid):,}')
        else:
            await modify_cash(uid, -bet, member)
            S.bot_stats['gamble_losses'] += 1
            await rogue_send(ctx, f'{member.mention} lost **${bet:,}**. balance: ${S.get_cash(uid):,}')

    @commands.hybrid_command(name='beg', description='Beg for a small random amount of cash.')
    async def beg(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        remaining = S.get_remaining_cooldown(S.last_beg.get(uid, 0), S.BEG_COOLDOWN)
        if remaining > 0:
            await rogue_send(ctx, f'Beg again in **{S.fmt_seconds(remaining)}**.')
            return
        import random
        reward = random.randint(S.BEG_MIN, S.BEG_MAX)
        S.last_beg[uid] = int(time.time())
        await modify_cash(uid, reward, ctx.author)
        await rogue_send(ctx, f'{ctx.author.mention} begged and got **${reward}**. balance: ${S.get_cash(uid):,}')

    @commands.hybrid_command(name='work', description='Work for a random cash payment.')
    async def work(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        remaining = S.get_remaining_cooldown(S.last_work.get(uid, 0), S.WORK_COOLDOWN)
        if remaining > 0:
            await rogue_send(ctx, f'Work again in **{S.fmt_seconds(remaining)}**.')
            return
        import random
        reward = random.randint(S.WORK_MIN, S.WORK_MAX)
        S.last_work[uid] = int(time.time())
        await modify_cash(uid, reward, ctx.author)
        await rogue_send(ctx, f'{ctx.author.mention} worked and earned **${reward}**. balance: ${S.get_cash(uid):,}')

    @commands.hybrid_command(name='pray', description='Pray for a chance at cash; failure can add debt.')
    async def pray(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        remaining = S.get_remaining_cooldown(S.last_pray.get(uid, 0), S.PRAY_COOLDOWN)
        if remaining > 0:
            await rogue_send(ctx, f'Pray again in **{S.fmt_seconds(remaining)}**.')
            return
        import random
        S.last_pray[uid] = int(time.time())
        if random.random() < S.PRAY_SUCCESS_CHANCE:
            reward = random.randint(S.PRAY_MIN, S.PRAY_MAX)
            await modify_cash(uid, reward, ctx.author)
            await rogue_send(ctx, f'{ctx.author.mention} prayed and received **${reward}**. balance: ${S.get_cash(uid):,}')
        else:
            debt = random.randint(20, 100)
            S.user_debt[uid] = S.get_debt(uid) + debt
            await rogue_send(ctx, f'{ctx.author.mention} prayed but gained **${debt} debt**. balance: ${S.get_cash(uid):,} | debt: ${S.get_debt(uid):,}')
            await S.save_cash_data()

    @commands.hybrid_command(name='debt', description='Show your current debt and overdue-penalty timing.')
    async def debt(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        debt = S.get_debt(uid)
        remaining = S.get_remaining_cooldown(S.last_debt_penalty.get(uid, 0), S.DEBT_PENALTY_INTERVAL_SECONDS)
        await rogue_send(ctx, f'{ctx.author.mention}: debt **${debt:,}**. next penalty in **{S.fmt_seconds(remaining)}**.')

    @commands.hybrid_command(name='loan', description='Borrow cash within the loan limits and receive debt with interest.')
    async def loan(self, ctx, amount: int):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        remaining = S.get_remaining_cooldown(S.last_loan.get(uid, 0), S.LOAN_COOLDOWN)
        if remaining > 0:
            await rogue_send(ctx, f'Loan again in **{S.fmt_seconds(remaining)}**.')
            return
        if amount < S.LOAN_MIN or amount > S.LOAN_MAX:
            await rogue_send(ctx, f'Loan amount must be between ${S.LOAN_MIN} and ${S.LOAN_MAX}.')
            return
        S.last_loan[uid] = int(time.time())
        debt_added = int(amount * (1 + S.LOAN_INTEREST_RATE))
        await modify_cash(uid, amount, ctx.author)
        S.user_debt[uid] = S.get_debt(uid) + debt_added
        await S.save_cash_data()
        await rogue_send(ctx, f'{ctx.author.mention} borrowed **${amount:,}**. debt added: **${debt_added:,}** (interest 20%). total debt: ${S.get_debt(uid):,}')

    @commands.hybrid_command(name='repay', description='Pay your debt using your cash balance.')
    async def repay(self, ctx, amount: str):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        debt = S.get_debt(uid)
        if debt <= 0:
            await rogue_send(ctx, 'you have no debt to repay.')
            return
        if amount.lower() == 'all':
            pay = min(debt, S.get_cash(uid))
        else:
            try:
                pay = int(amount.replace(',', '').replace('$', ''))
            except ValueError:
                await rogue_send(ctx, 'amount must be a number or `all`.')
                return
        if pay <= 0:
            await rogue_send(ctx, 'repay amount must be more than 0.')
            return
        balance = S.get_cash(uid)
        if balance < pay:
            await rogue_send(ctx, f'you only have ${balance:,}.')
            return
        await modify_cash(uid, -pay, ctx.author)
        S.user_debt[uid] = max(0, debt - pay)
        await S.save_cash_data()
        await rogue_send(ctx, f'{ctx.author.mention} repaid **${pay:,}** debt. remaining debt: ${S.get_debt(uid):,} | balance: ${S.get_cash(uid):,}')

    @commands.hybrid_command(name='give', description='Transfer your cash to another citizen.')
    async def give(self, ctx, member: discord.Member, amount: str):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        tid = member.id
        if tid == uid:
            await rogue_send(ctx, 'you cannot give cash to yourself.')
            return
        if S.is_protected(tid):
            await rogue_send(ctx, f'{member.mention} is protected and cannot receive cash.')
            return
        if amount.lower() == 'all':
            pay = S.get_cash(uid)
        else:
            try:
                pay = int(amount.replace(',', '').replace('$', ''))
            except ValueError:
                await rogue_send(ctx, 'amount must be a number or `all`.')
                return
        if pay <= 0:
            await rogue_send(ctx, 'give amount must be more than 0.')
            return
        balance = S.get_cash(uid)
        if balance < pay:
            await rogue_send(ctx, f'you only have ${balance:,}.')
            return
        paid, _ = await debit_cash(uid, pay, ctx.author)
        if not paid:
            await rogue_send(ctx, f'you only have ${S.get_cash(uid):,}. no cash was transferred.')
            return
        await modify_cash(tid, pay, member)
        S.bot_stats['given'] += pay
        S.bot_stats['received'] += pay
        await S.save_cash_data()
        await rogue_send(ctx, f'{ctx.author.mention} gave **${pay:,}** to {member.mention}. your balance: ${S.get_cash(uid):,}')

    @commands.hybrid_command(name='steal', description='Attempt to steal cash; failure pays a penalty and raises wanted level.')
    async def steal(self, ctx, member: discord.Member, amount: str):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        tid = member.id
        if tid == uid:
            await rogue_send(ctx, 'you cannot steal from yourself.')
            return
        if S.is_protected(tid):
            await rogue_send(ctx, f'{member.mention} is protected and cannot be stolen from.')
            return
        target_balance = S.get_cash(tid)
        if target_balance <= 0:
            await rogue_send(ctx, f'{member.mention} has nothing to steal.')
            return
        if amount.lower() == 'all':
            bet = min(target_balance, S.STEAL_MAX)
        else:
            try:
                bet = int(amount.replace(',', '').replace('$', ''))
            except ValueError:
                await rogue_send(ctx, 'amount must be a number or `all`.')
                return
        if bet <= 0:
            await rogue_send(ctx, 'steal amount must be more than 0.')
            return
        bet = min(bet, target_balance, S.STEAL_MAX)
        thief_balance = S.get_cash(uid)
        success = random.random() < S.STEAL_SUCCESS_CHANCE
        if success:
            S.bot_stats['steal_success'] += 1
            await modify_cash(uid, bet, ctx.author)
            await modify_cash(tid, -bet, member)
            await rogue_send(ctx, f'{ctx.author.mention} stole **${bet:,}** from {member.mention}. balance: ${S.get_cash(uid):,}')
        else:
            penalty = max(1, int(bet * S.STEAL_FAIL_PENALTY_RATE))
            penalty = min(penalty, thief_balance)
            S.bot_stats['steal_fail'] += 1
            if penalty > 0:
                await modify_cash(uid, -penalty, ctx.author)
                await modify_cash(tid, penalty, member)
            S.add_wanted(uid, 1)
            await rogue_send(ctx, f'{ctx.author.mention} failed to steal from {member.mention} and paid **${penalty}**. wanted level: {S.get_wanted(uid)}')

    @commands.hybrid_command(name='botstats', description="Show Jachlam's economy and activity counters.")
    async def botstats(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        await rogue_send(ctx, (
            f'**Jachlam economy:** cash ${S.get_bot_cash():,} | tax collected ${S.bot_stats["tax_collected"]:,} | '
            f'gamble wins {S.bot_stats["gamble_wins"]} / losses {S.bot_stats["gamble_losses"]} | '
            f'steal success {S.bot_stats["steal_success"]} / fail {S.bot_stats["steal_fail"]} | '
            f'given ${S.bot_stats["given"]:,} / received ${S.bot_stats["received"]:,} | '
            f'messages seen {S.bot_stats["messages_seen"]} | replies {S.bot_stats["replies_sent"]}'
        ))

    @commands.hybrid_command(name='taxinfo', description='Show your current tax bracket and time until the next tax.')
    async def taxinfo(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        balance = S.get_cash(uid)
        rate = S.tax_rate_for_balance(balance)
        tax_amount = S.tax_amount_for_balance(balance)
        remaining = S.get_remaining_cooldown(S.last_tax.get(uid, 0), S.TAX_INTERVAL_SECONDS)
        await rogue_send(ctx, (
            f'{ctx.author.mention}: balance ${balance:,} | bracket {int(rate * 100)}% | '
            f'tax due ${tax_amount:,} | next tax in **{S.fmt_seconds(remaining)}**.'
        ))

    @commands.hybrid_command(name='evade', description='Evade the current tax assessment and add a recorded crime.')
    async def evade(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        if S.is_protected(uid):
            await rogue_send(ctx, 'protected users cannot evade tax.')
            return
        tax_amount, rate, remaining = S.get_tax_due(uid, ignore_timer=True)
        if tax_amount <= 0:
            await rogue_send(ctx, 'no tax is currently due to evade.')
            return
        S.tax_evasion_count[uid] = S.tax_evasion_count.get(uid, 0) + 1
        S.tax_evasion_debt[uid] = True
        S.record_crime(uid, 'tax_evasion')
        S.last_tax[uid] = int(time.time())
        S.SHOP_ITEMS  # noqa: keep reference
        await rogue_send(ctx, f'{ctx.author.mention} evaded **${tax_amount:,}** tax ({int(rate * 100)}%). recorded crime: tax evasion.')

    @commands.hybrid_command(name='forcetaxall', description='Make every loaded account immediately process its tax.')
    async def forcetaxall(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        if not S.is_money_admin(ctx.author.id):
            permissions = getattr(ctx.author, 'guild_permissions', None)
            if not (permissions and permissions.administrator):
                await rogue_send(ctx, 'not allowed')
                return
        total_collected = 0
        users_taxed = 0
        for uid in list(S.user_cash.keys()):
            S.last_tax[uid] = 0
            tax_amount, _rate = await apply_tax_if_due(uid, ctx.guild.get_member(uid))
            users_taxed += 1
            if tax_amount > 0:
                total_collected += tax_amount
        await rogue_send(ctx, f'forced tax on {users_taxed} users, collected ${total_collected}')


async def setup(bot):
    await bot.add_cog(Economy(bot))
