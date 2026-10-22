"""Jachlam Shop Cog — slash commands for buying, inventory, and item use."""

import random
import discord
from discord.ext import commands

from cogs import state as S
from cogs.core import set_cash, modify_cash, rogue_send
from cogs.state import debit_cash
from cogs.state import (
    SHOP_ITEMS, ANDY_USER_ID, ORION_USER_ID, get_inventory, add_item, remove_item,
    get_item_qty, get_protection_remaining, save_inventory_data,
    apply_daily_events,
)


def find_shop_item(query):
    """Match by item_id or by (case-insensitive) display name."""
    query = query.strip().lower().replace(' ', '_')
    if query in S.SHOP_ITEMS:
        return query
    for item_id, item in S.SHOP_ITEMS.items():
        if item['name'].lower().replace(' ', '_') == query:
            return item_id
    return None


class Shop(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @commands.hybrid_command(name='shop', description='List every shop item, price, ID, and effect.')
    async def shop(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        lines = [
            f"**{item['name']}** (`{item_id}`) \u2014 ${item['price']} \u2014 {item['description']}"
            for item_id, item in S.SHOP_ITEMS.items()
        ]
        embed = discord.Embed(
            title='shop',
            description='\n'.join(lines) + '\n\nbuy with `/buy <item> [qty]`, use with `/use <item>`',
            color=discord.Color.blurple(),
        )
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='buy', description='Buy an item; guns and knives become assassination charges.')
    async def buy(self, ctx, item_name: str, qty: int = 1):
        if not S.is_active_channel(ctx.channel):
            return
        if qty <= 0:
            await rogue_send(ctx, 'quantity must be more than 0')
            return
        item_id = find_shop_item(item_name)
        if item_id is None:
            await rogue_send(ctx, f"no item called '{item_name}'. check `/shop` for what's available.")
            return
        item = S.SHOP_ITEMS[item_id]
        cost = item['price'] * qty
        uid = ctx.author.id
        kind = item['kind']
        if kind in {'andy', 'brick'} and qty != 1:
            await rogue_send(ctx, f"you can only buy 1 {item['name']} at a time")
            return
        if kind == 'brick' and uid in S.brick_active:
            await rogue_send(ctx, 'you already have an active Brick')
            return
        paid, remaining_balance = await debit_cash(uid, cost, ctx.author)
        if not paid:
            await rogue_send(ctx, f'that costs ${cost:,} and you only have ${remaining_balance:,}. no item was granted.')
            return
        if kind == 'assassin_weapon':
            charges = item['assassin_charges'] * qty
            S.assassin_charges[uid] = S.get_assassin_charges(uid) + charges
            await S.save_inventory_data()
            await rogue_send(
                ctx, f"bought {qty}x **{item['name']}** for ${cost}. assassination charges: {S.get_assassin_charges(uid)}. "
                f"use with `/use {item_id} @user` or `/assassinate @user`. balance: ${S.get_cash(uid)}"
            )
            await apply_daily_events(ctx, {'buy': qty})
            return
        if kind == 'andy':
            if S.ANDY_USER_ID is not None:
                cut = max(1, int(S.get_cash(uid) * 0.1))
                await modify_cash(uid, -cut)
                await modify_cash(S.ANDY_USER_ID, cut)
            await rogue_send(ctx, f"bought {qty}x **{item['name']}** for ${cost}. balance: ${S.get_cash(uid)}")
            await apply_daily_events(ctx, {'buy': qty})
            return
        if kind == 'brick':
            S.brick_active.add(uid)
            await S.save_inventory_data()
            await rogue_send(
                ctx, f"bought {qty}x **{item['name']}** for ${cost}. your displayed balance is now inflated "
                f"{item['display_multiplier']}x -- everyone's going to think you're loaded."
            )
            await apply_daily_events(ctx, {'buy': qty})
            return
        S.add_item(uid, item_id, qty)
        await S.save_inventory_data()
        await rogue_send(
            ctx, f"bought {qty}x **{item['name']}** for ${cost}. you now have {S.get_item_qty(uid, item_id)}x. "
            f"balance: ${S.get_cash(uid)}"
        )
        await apply_daily_events(ctx, {'buy': qty})

    @commands.hybrid_command(name='inventory', description='Show items, assassination charges, and active effects.')
    async def inventory(self, ctx, member: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        target = member or ctx.author
        inv = S.get_inventory(target.id)
        charges = S.get_assassin_charges(target.id)
        if not inv and charges <= 0:
            await rogue_send(ctx, f'{target.mention} has nothing in their inventory')
            return
        lines = [f"**{S.SHOP_ITEMS[item_id]['name']}** x{qty}" for item_id, qty in inv.items() if item_id in S.SHOP_ITEMS]
        if charges > 0:
            lines.append(f'\U0001f52a assassination charges: {charges}')
        protection_remaining = S.get_protection_remaining(target.id)
        if protection_remaining > 0:
            lines.append(f'\n\U0001f6e1\ufe0f protected for {S.fmt_seconds(protection_remaining)}')
        embed = discord.Embed(title=f"{target.display_name}'s inventory", description='\n'.join(lines), color=discord.Color.green())
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='use', description='Use an inventory item or spend a gun/knife assassination charge.')
    async def use(self, ctx, item_name: str, member: discord.Member = None, amount: int = 1):
        if not S.is_active_channel(ctx.channel):
            return
        item_id = find_shop_item(item_name)
        if item_id is None:
            await rogue_send(ctx, f"no item called '{item_name}'.")
            return
        item = S.SHOP_ITEMS[item_id]
        uid = ctx.author.id
        kind = item['kind']
        if kind == 'assassin_weapon':
            if S.get_assassin_charges(uid) < 1:
                await rogue_send(ctx, 'you have no assassination charges.')
                return
            if member is None:
                await rogue_send(ctx, 'usage: `/use gun @user`')
                return
            S.assassin_charges[uid] = S.get_assassin_charges(uid) - 1
            await rogue_send(ctx, f'{ctx.author.mention} spent a charge on {member.mention}. charges remaining: {S.get_assassin_charges(uid)}')
            await S.save_inventory_data()
            return
        if kind == 'mystery_box':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, 'you do not own a Mystery Box.')
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            prize = random.randint(item['box_min'], item['box_max'])
            await modify_cash(uid, prize, ctx.author)
            await rogue_send(ctx, f'{ctx.author.mention} opened a Mystery Box and found **${prize}**. balance: ${S.get_cash(uid):,}')
            return
        if kind == 'lucky_charm':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, 'you do not own a Lucky Charm.')
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            S.luck_drug_until[uid] = time.time() + 300
            await rogue_send(ctx, f'{ctx.author.mention} used a Lucky Charm. next /gamble has +35% win chance for 5 minutes.')
            return
        if kind == 'debt_relief':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, 'you do not own a Debt Relief Voucher.')
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            relief = item['debt_amount']
            S.user_debt[uid] = max(0, S.get_debt(uid) - relief)
            await S.save_cash_data()
            await rogue_send(ctx, f'{ctx.author.mention} used a Debt Relief Voucher. ${relief} debt cleared. remaining: ${S.get_debt(uid):,}')
            return
        if kind == 'double_money':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, "you do not own Jachlam's Blessing.")
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            await set_cash(uid, S.get_cash(uid) * 2, ctx.author, force_nick=True)
            await rogue_send(ctx, f"{ctx.author.mention} used Jachlam's Blessing. cash doubled to ${S.get_cash(uid):,}.")
            return
        if kind == 'punish_orion':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, "you do not own Jachlam's Punishment.")
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            S.user_debt[S.ORION_USER_ID] = S.get_debt(S.ORION_USER_ID) + item['debt_amount']
            await S.save_cash_data()
            await rogue_send(ctx, f"{ctx.author.mention} used Jachlam's Punishment. Orion gained ${item['debt_amount']} debt.")
            return
        if kind == 'giant_turd':
            if S.get_item_qty(uid, item_id) < 1:
                await rogue_send(ctx, 'you do not own a Giant Turd.')
                return
            if member is None:
                await rogue_send(ctx, 'usage: `/use giant_turd @user`')
                return
            S.remove_item(uid, item_id, 1)
            await S.save_inventory_data()
            await rogue_send(ctx, f'{ctx.author.mention} hurled a Giant Turd at {member.mention}. it does nothing. glorious.')
            return
        await rogue_send(ctx, f'{item["name"]} cannot be used directly.')


async def setup(bot):
    await bot.add_cog(Shop(bot))


import time
