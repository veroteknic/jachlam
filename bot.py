import asyncio
import discord
from discord.ext import commands
import aiofiles
import aiohttp
import random
import os
import json
import re
import shutil
import sys
import time
from datetime import timedelta
from datetime import datetime
from collections import deque
from zoneinfo import ZoneInfo
from dotenv import load_dotenv
load_dotenv()
TOKEN = os.getenv('DISCORD_TOKEN') or os.getenv('TOKEN')
CHANNEL_ID_DEFAULT = 1409844931761279019
MONEY_ADMIN_USER_ID = 1055064009457537024
TEXT_FILE = 'markov_corpus.txt'
CASH_FILE = 'cash_data.json'
INVENTORY_FILE = 'inventory_data.json'
CORPUS_QUOTE_PREFIX = 'Q:'
tax_evasion_count = {}
DEBUG = True
SEEN_GIFS_FILE = 'seen_gifs.json'
MAX_PHRASES = 400
MAX_RECENT_PHRASES = 80
MAX_RECENT_SENTENCES = 15
MAX_REPLY_PHRASES = 3
SILENCE_CHANCE = 0.3
MAX_TRACK_LINES = 30000
MAX_CORPUS_LINES = 12000
QUOTES_PAGE_SIZE = 5
TRACK_DURATION = 300
JACHLAM_VERSION = '2026.08.23-r6'
STARTING_CASH = 500
GAMBLE_WIN_CHANCE = 0.48
BEG_MIN = 15
BEG_MAX = 60
BEG_COOLDOWN = 60
WORK_MIN = 80
WORK_MAX = 220
WORK_COOLDOWN = 300
PRAY_MIN = 40
PRAY_MAX = 180
PRAY_COOLDOWN = 120
PRAY_SUCCESS_CHANCE = 0.42
LOAN_MIN = 100
LOAN_MAX = 5000
LOAN_COOLDOWN = 3600
LOAN_INTEREST_RATE = 0.2
DEBT_PENALTY_INTERVAL_SECONDS = 6 * 60 * 60
DEBT_PENALTY_CASH_FEE = 15
DEBT_PENALTY_DEBT_RATE = 0.03
TAX_INTERVAL_SECONDS = 60 * 60
STEAL_SUCCESS_CHANCE = 0.38
STEAL_FAIL_PENALTY_RATE = 0.25
BOT_AUTO_ECONOMY_ENABLED = True
BOT_AUTO_MIN_DELAY = 180
BOT_AUTO_MAX_DELAY = 480
BOT_AUTO_TRIGGER_CHANCE = 0.35
BOT_GAMBLE_BET_MIN = 25
BOT_GAMBLE_BET_MAX = 200
BOT_SOCIAL_ACTION_CHANCE = 0.45
BOT_GIVE_MIN = 20
BOT_GIVE_MAX = 120
BOT_STEAL_MIN = 20
BOT_STEAL_MAX = 120
BOT_MIN_BALANCE_FOR_SOCIAL = 80
ASSASSINATE_COST = 10000
ASSASSINATE_SUCCESS_CHANCE = 0.5
ASSASSINATE_FAIL_PENALTY = 15000
ASSASSINATE_TIMEOUT_SECONDS = 2 * 60 * 60
ASSASSINATE_COOLDOWN = 600
last_assassinate = {}
last_assassinated_at = {}
NICK_EDIT_MIN_INTERVAL = 20
last_nick_edit = {}
ADMIN_USER_IDS = {MONEY_ADMIN_USER_ID}
ANDY_USER_ID = 1091302334618939422
SHOP_ITEMS = {'shield': {'name': 'Shield', 'price': 250, 'description': 'protects you from !steal and !assassinate for 1 hour', 'kind': 'shield', 'shield_hours': 1}, 'super_shield': {'name': 'Super Shield', 'price': 750, 'description': 'protects you from !steal and !assassinate for 6 hours', 'kind': 'shield', 'shield_hours': 6}, 'lucky_charm': {'name': 'Lucky Charm', 'price': 500, 'description': "boosts your next !gamble's win chance by 35% (not a guaranteed win)", 'kind': 'lucky_charm', 'boost': 0.35}, 'debt_relief': {'name': 'Debt Relief Voucher', 'price': 400, 'description': 'clears $1000 of debt', 'kind': 'debt_relief', 'debt_amount': 1000}, 'mystery_box': {'name': 'Mystery Box', 'price': 300, 'description': 'opens into a random amount of cash ($0-$1000)', 'kind': 'mystery_box', 'box_min': 0, 'box_max': 1000}, 'knife': {'name': 'Knife', 'price': 150, 'description': 'grants you 1 use of !assassinate', 'kind': 'assassin_weapon', 'assassin_charges': 1}, 'gun': {'name': 'Gun', 'price': 250, 'description': 'grants you 2 uses of !assassinate', 'kind': 'assassin_weapon', 'assassin_charges': 2}, 'mystery_pack': {'name': 'Mysterious Pack', 'price': 350, 'description': "who knows what's in it -- cash, debt, or worse. use at your own risk", 'kind': 'mystery_pack'}, 'giant_turd': {'name': 'Giant Turd', 'price': 100, 'description': 'does nothing, but you can hurl it at someone with `!use giant_turd @user`', 'kind': 'novelty'}, 'andy': {'name': 'Andy', 'price': 15, 'description': '???', 'kind': 'andy'}, 'jachlams_blessing': {'name': "Jachlam's Blessing", 'price': 600, 'description': 'one-time use: doubles your current cash', 'kind': 'double_money'}, 'brick': {'name': 'Brick', 'price': 900, 'description': 'does nothing, except your displayed balance shows 3x higher -- good luck with that', 'kind': 'brick', 'display_multiplier': 3}, 'jachlams_punishment': {'name': "Jachlam's Punishment", 'price': 75, 'description': 'gives Orion $1000 debt', 'kind': 'punish_orion', 'debt_amount': 1000}, 'mystery_drug': {'name': 'Mysterious Drug', 'price': 700, 'description': 'some kind of substance. temporarily improves your !gamble luck', 'kind': 'luck_drug', 'luck_hours': 1, 'luck_boost': 0.2}}
MYSTERY_DRUG_FLAVORS = ['a suspicious white powder', 'a handful of unlabeled pills', 'some kind of green herb', 'a vial of glowing liquid', 'energy drink concentrate (probably)', 'questionable gas station pills']
user_inventory = {}
inventory_file_lock = asyncio.Lock()
protected_until = {}
lucky_charm_active = set()
assassin_charges = {}
brick_active = set()
luck_drug_until = {}

def get_assassin_charges(uid):
    return assassin_charges.get(int(uid), 0)

def get_display_cash(uid):
    """The number shown in nicknames/!cash -- inflated 3x if the user has
    an active Brick, otherwise identical to their real balance."""
    uid = int(uid)
    real = get_cash(uid)
    if uid in brick_active:
        return real * SHOP_ITEMS['brick']['display_multiplier']
    return real

def has_luck_boost(uid):
    return luck_drug_until.get(int(uid), 0) > time.time()
ORION_USER_ID = 1388459209431187557
GIF_REPEAT_TIMEOUT_DAYS = 7
seen_gif_keys = set()
NUKE_TIMEOUT_DAYS = 7
NUKE_CONFIRM_WINDOW = 20
pending_nukes = {}
TAX_BRACKETS = [(20000, 0.1), (10000, 0.07), (5000, 0.04), (1000, 0.02), (0, 0.0)]
FALLBACKS = ['dang same', 'yo fr', 'ehh idk', '\U0001f62d']
AWST = ZoneInfo('Australia/Perth')
BEDTIME_START_HOUR = 22
BEDTIME_END_HOUR = 7
bot_is_asleep = False
sleep_override = None

def is_bedtime():
    if sleep_override is not None:
        return sleep_override
    hour = datetime.now(AWST).hour
    return hour >= BEDTIME_START_HOUR or hour < BEDTIME_END_HOUR

def debug(msg):
    if DEBUG:
        print(f'[DEBUG] {msg}')

def boot_banner():
    """Print the startup banner using ASCII-safe terminal escape codes."""
    red = '\x1b[91m'
    dim = '\x1b[2m'
    reset = '\x1b[0m'
    print(red + '=' * 58)
    print('       J  A  C  H  L  A  M   //   SYSTEM BOOT')
    print(f'       VERSION {JACHLAM_VERSION}   |   ECONOMY CORE')
    print('=' * 58 + reset)
    print(dim + '[ WAKE SIGNAL ACCEPTED // BEGIN INITIALIZATION ]' + reset)

def boot_status(system, detail='ONLINE'):
    print(f'[BOOT] {system:<24} [ {detail} ]')
intents = discord.Intents.default()
intents.message_content = True
intents.members = True
bot = commands.Bot(command_prefix='!', intents=intents)
cash_file_lock = asyncio.Lock()
background_tasks = []
tasks_started = False
shutdown_started = False
user_pools = {}
user_full_lines = {}
user_quotes = {}
recent_sentences = []
user_cash = {}
user_debt = {}
tax_evasion_debt = {}
last_beg = {}
last_work = {}
last_pray = {}
last_loan = {}
last_debt_penalty = {}
last_tax = {}
bot_user_id = None
CHANNEL_ID = CHANNEL_ID_DEFAULT
SERVER_WIDE_MODE = True
EXCLUDED_CHANNEL_IDS = set()
bot_stats = {'messages_seen': 0, 'replies_sent': 0, 'tax_collected': 0, 'gamble_wins': 0, 'gamble_losses': 0, 'steal_success': 0, 'steal_fail': 0, 'given': 0, 'received': 0}
reaction_starts = []
reaction_middles = []
reaction_ends = []
MAX_REACTIONS = 200
message_counter = 0
messages_per_reply = random.randint(1, 5)
corpus_line_count = 0
mode = 'global'
track_target = None

def can_use_assassinate(uid):
    if is_money_admin(uid):
        return (True, 0)
    remaining = get_remaining_cooldown(last_assassinate.get(uid, 0), ASSASSINATE_COOLDOWN)
    return (remaining == 0, remaining)

def get_assassination_protection(target_id):
    """Seconds remaining before a recently-hit target can be assassinated again."""
    return get_remaining_cooldown(last_assassinated_at.get(target_id, 0), ASSASSINATE_TIMEOUT_SECONDS)

def is_active_channel(channel):
    """Whether the bot should read/respond/run commands in this channel.

    SERVER_WIDE_MODE (default on): every text channel in the guild, minus
    anything explicitly excluded. When off, only CHANNEL_ID (the original
    single-channel behavior) is active -- useful if someone wants to dial
    it back down to one channel later via !setup.
    """
    if channel is None or not isinstance(channel, (discord.TextChannel, discord.Thread)):
        return False
    if channel.id in EXCLUDED_CHANNEL_IDS:
        return False
    if SERVER_WIDE_MODE:
        return True
    return channel.id == CHANNEL_ID

def get_active_text_channels(guild):
    """All channels the bot is currently active in for a given guild."""
    if guild is None:
        return []
    if SERVER_WIDE_MODE:
        return [c for c in guild.text_channels if c.id not in EXCLUDED_CHANNEL_IDS and c.permissions_for(guild.me).send_messages]
    channel = guild.get_channel(CHANNEL_ID)
    if channel is not None and channel.id not in EXCLUDED_CHANNEL_IDS:
        return [channel]
    return []

def is_valid_phrase(text):
    if text.startswith('!'):
        return False
    if '\n' in text:
        return False
    words = text.split()
    return 2 <= len(words) <= 12

def remix_phrase(a, b):
    wa = a.split()
    wb = b.split()
    cut = random.randint(1, min(len(wa), len(wb)) - 1)
    return ' '.join(wa[:cut] + wb[cut:])

def _clean_display_name(name):
    return re.sub('^\\[\\$?\\d+\\]\\s*', '', name)

async def update_cash_nick(member, cash, force=False):
    if member is None or not isinstance(member, discord.Member):
        return
    if member.guild is None:
        return
    cleaned = _clean_display_name(member.display_name)
    prefix = f'[${cash}] '
    max_name_len = max(1, 32 - len(prefix))
    new_nick = f'{prefix}{cleaned[:max_name_len]}'
    if member.nick == new_nick:
        return
    if not force:
        remaining = get_remaining_cooldown(last_nick_edit.get(member.id, 0), NICK_EDIT_MIN_INTERVAL)
        if remaining > 0:
            debug(f'Nick edit throttled for {member.display_name} ({remaining}s left)')
            return
    try:
        await member.edit(nick=new_nick, reason='Cash display update')
        last_nick_edit[member.id] = int(time.time())
    except discord.Forbidden:
        debug(f'No permission to edit nickname for {member.display_name}')
    except discord.HTTPException:
        debug(f'Failed to edit nickname for {member.display_name}')

def get_cash(uid):
    uid = int(uid)
    if uid not in user_cash:
        user_cash[uid] = STARTING_CASH
    return user_cash[uid]

def get_bot_cash():
    if bot_user_id is None:
        return 0
    return get_cash(bot_user_id)

def get_debt(uid):
    uid = int(uid)
    if uid not in user_debt:
        user_debt[uid] = 0
    return user_debt[uid]

def clear_user_state(uid):
    uid = int(uid)
    user_cash[uid] = STARTING_CASH
    user_debt[uid] = 0
    tax_evasion_debt.pop(uid, None)
    last_beg.pop(uid, None)
    last_work.pop(uid, None)
    last_pray.pop(uid, None)
    last_loan.pop(uid, None)
    last_debt_penalty.pop(uid, None)
    last_tax.pop(uid, None)
    last_assassinate.pop(uid, None)
    last_assassinated_at.pop(uid, None)
    user_inventory.pop(uid, None)
    protected_until.pop(uid, None)
    lucky_charm_active.discard(uid)
    assassin_charges.pop(uid, None)
    brick_active.discard(uid)
    luck_drug_until.pop(uid, None)

def is_money_admin(uid):
    return int(uid) in ADMIN_USER_IDS

def admin_check():
    """Single reusable permission check for all admin-gated commands."""

    async def predicate(ctx):
        return is_money_admin(ctx.author.id)
    return commands.check(predicate)

async def resolve_member_and_amount(ctx, first: str, second: str):
    converter = commands.MemberConverter()
    try:
        member = await converter.convert(ctx, first)
        amount = int(second)
        return (member, amount)
    except (commands.BadArgument, ValueError):
        pass
    try:
        member = await converter.convert(ctx, second)
        amount = int(first)
        return (member, amount)
    except (commands.BadArgument, ValueError):
        return (None, None)

def get_tax_due(uid, ignore_timer=False):
    uid = int(uid)
    remaining = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)
    if remaining > 0 and (not ignore_timer):
        return (0, 0.0, remaining)
    balance = get_cash(uid)
    rate = tax_rate_for_balance(balance)
    tax_amount = tax_amount_for_balance(balance)
    return (tax_amount, rate, remaining)

async def set_cash(uid, amount, member=None, force_nick=False):
    uid = int(uid)
    user_cash[uid] = max(0, int(amount))
    if member is None and bot_user_id == uid:
        for guild in bot.guilds:
            member = guild.get_member(uid)
            if member:
                break
    if member:
        await update_cash_nick(member, get_display_cash(uid), force=force_nick)
    await save_cash_data()
cash_locks = {}

def get_cash_lock(uid):
    uid = int(uid)
    lock = cash_locks.get(uid)
    if lock is None:
        lock = asyncio.Lock()
        cash_locks[uid] = lock
    return lock

async def modify_cash(uid, delta, member=None, force_nick=False):
    """Atomically apply a +/- delta to a user's cash.

    Fixes a real bug: several commands used to do `balance = get_cash(uid)`
    then, after other awaits (nickname edits, file saves, message sends),
    call `set_cash(uid, balance +/- amount, ...)`. If a second command for
    the same user finished its own read-modify-write in between, that
    second change would silently get overwritten -- e.g. someone !buy's an
    item (cash goes down), but a concurrent !gamble/!give/!work finishing
    around the same time re-reads the pre-purchase balance and stomps the
    deduction back, making it look like "shop money doesn't take". Locking
    per-user around the read+write closes that window.
    """
    async with get_cash_lock(uid):
        balance = get_cash(uid)
        new_balance = max(0, balance + delta)
        await set_cash(uid, new_balance, member, force_nick=force_nick)
        return new_balance

async def set_cash_locked(uid, amount, member=None, force_nick=False):
    """Lock-protected absolute set, for admin overrides that shouldn't race
    with a concurrent modify_cash() on the same account."""
    async with get_cash_lock(uid):
        await set_cash(uid, amount, member, force_nick=force_nick)
        return get_cash(uid)

async def load_seen_gif_keys():
    global seen_gif_keys
    try:
        with open(SEEN_GIFS_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        seen_gif_keys = set(data)
    except FileNotFoundError:
        seen_gif_keys = set()
    except (json.JSONDecodeError, TypeError):
        debug('seen_gifs.json is invalid, starting with empty GIF history')
        seen_gif_keys = set()

async def save_seen_gif_keys():
    with open(SEEN_GIFS_FILE, 'w', encoding='utf-8') as f:
        json.dump(list(seen_gif_keys), f, indent=2)

def parse_int_dict(data, key, minimum=None):
    """Validate and return a JSON object with integer keys and values."""
    parsed = {}
    for raw_uid, raw_value in data.get(key, {}).items():
        try:
            uid = int(raw_uid)
            value = int(raw_value)
        except (TypeError, ValueError):
            continue
        parsed[uid] = max(minimum, value) if minimum is not None else value
    return parsed

async def read_json_file(path, label):
    """Read a JSON object without silently accepting damaged save data."""
    try:
        async with aiofiles.open(path, 'r', encoding='utf-8') as f:
            raw = await f.read()
    except FileNotFoundError:
        return None
    if not raw.strip():
        raise ValueError(f'{label} is blank')
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f'{label} contains invalid JSON') from exc
    if not isinstance(data, dict):
        raise ValueError(f'{label} must contain a JSON object')
    return data

async def atomic_save_json(path, payload, lock, label):
    """Write JSON safely without leaving a partial file after a forced stop."""
    temp_path = f'{path}.tmp'
    async with lock:
        try:
            encoded = json.dumps(payload, ensure_ascii=True, separators=(',', ':'))
            async with aiofiles.open(temp_path, 'w', encoding='utf-8') as f:
                await f.write(encoded)
            if os.path.exists(path):
                shutil.copy2(path, f'{path}.bak')
            os.replace(temp_path, path)
        except OSError as exc:
            debug(f'Failed to save {label}: {exc}')
            return False
    return True

async def load_cash_data(allow_empty=True):
    global CHANNEL_ID, SERVER_WIDE_MODE, EXCLUDED_CHANNEL_IDS
    data = await read_json_file(CASH_FILE, 'cash_data.json')
    if data is None:
        return False
    if 'cash' not in data or not isinstance(data['cash'], dict):
        raise ValueError("cash_data.json has no valid 'cash' section")
    non_negative_maps = {'cash': user_cash, 'debt': user_debt, 'tax_evasion_count': tax_evasion_count}
    timestamp_maps = {'last_beg': last_beg, 'last_work': last_work, 'last_pray': last_pray, 'last_loan': last_loan, 'last_debt_penalty': last_debt_penalty, 'last_tax': last_tax}
    parsed_non_negative = {key: parse_int_dict(data, key, minimum=0) for key in non_negative_maps}
    parsed_timestamps = {key: parse_int_dict(data, key) for key in timestamp_maps}
    if not allow_empty and user_cash and (not parsed_non_negative['cash']):
        raise ValueError('cash_data.json contains no balances; refusing to erase live balances')
    for key, target in non_negative_maps.items():
        target.clear()
        target.update(parsed_non_negative[key])
    for key, target in timestamp_maps.items():
        target.clear()
        target.update(parsed_timestamps[key])
    tax_evasion_debt.clear()
    for raw_uid, value in data.get('tax_evasion_debt', {}).items():
        try:
            tax_evasion_debt[int(raw_uid)] = bool(value)
        except (TypeError, ValueError):
            continue
    loaded_bot_stats = data.get('bot_stats', {})
    for key in bot_stats.keys():
        try:
            bot_stats[key] = int(loaded_bot_stats.get(key, bot_stats[key]))
        except (TypeError, ValueError):
            continue
    loaded_channel_id = data.get('channel_id')
    if loaded_channel_id is not None:
        try:
            CHANNEL_ID = int(loaded_channel_id)
        except (TypeError, ValueError):
            pass
    loaded_server_wide = data.get('server_wide_mode')
    if loaded_server_wide is not None:
        SERVER_WIDE_MODE = bool(loaded_server_wide)
    loaded_excluded = data.get('excluded_channel_ids', [])
    cleaned_excluded = set()
    for cid in loaded_excluded:
        try:
            cleaned_excluded.add(int(cid))
        except (TypeError, ValueError):
            continue
    EXCLUDED_CHANNEL_IDS = cleaned_excluded
    debug(f'Cash data loaded ({len(user_cash)} balances)')
    return True

async def load_inventory_data():
    data = await read_json_file(INVENTORY_FILE, 'inventory_data.json')
    if data is None:
        return
    user_inventory.clear()
    for uid, items in data.get('inventory', {}).items():
        try:
            uid_int = int(uid)
        except (TypeError, ValueError):
            continue
        cleaned = {}
        for item_id, qty in (items or {}).items():
            if item_id not in SHOP_ITEMS:
                continue
            try:
                qty_int = int(qty)
            except (TypeError, ValueError):
                continue
            if qty_int > 0:
                cleaned[item_id] = qty_int
        if cleaned:
            user_inventory[uid_int] = cleaned
    for key, target, minimum in (('protected_until', protected_until, None), ('assassin_charges', assassin_charges, 0), ('luck_drug_until', luck_drug_until, None)):
        target.clear()
        target.update(parse_int_dict(data, key, minimum=minimum))
    lucky_charm_active.clear()
    brick_active.clear()
    for values, target in ((data.get('lucky_charm_active', []), lucky_charm_active), (data.get('brick_active', []), brick_active)):
        for uid in values:
            try:
                target.add(int(uid))
            except (TypeError, ValueError):
                continue
    debug('Inventory data loaded')

async def save_inventory_data():
    payload = {'inventory': {str(uid): items for uid, items in user_inventory.items() if items}, 'protected_until': {str(uid): ts for uid, ts in protected_until.items()}, 'lucky_charm_active': [str(uid) for uid in lucky_charm_active], 'assassin_charges': {str(uid): charges for uid, charges in assassin_charges.items() if charges}, 'brick_active': [str(uid) for uid in brick_active], 'luck_drug_until': {str(uid): ts for uid, ts in luck_drug_until.items()}}
    return await atomic_save_json(INVENTORY_FILE, payload, inventory_file_lock, 'inventory data')

def get_inventory(uid):
    uid = int(uid)
    return user_inventory.setdefault(uid, {})

def get_item_qty(uid, item_id):
    return get_inventory(uid).get(item_id, 0)

def add_item(uid, item_id, qty=1):
    inv = get_inventory(uid)
    inv[item_id] = inv.get(item_id, 0) + qty

def remove_item(uid, item_id, qty=1):
    inv = get_inventory(uid)
    if inv.get(item_id, 0) < qty:
        return False
    inv[item_id] -= qty
    if inv[item_id] <= 0:
        inv.pop(item_id, None)
    return True

def get_protection_remaining(uid):
    remaining = protected_until.get(int(uid), 0) - time.time()
    return max(0, int(remaining))

async def save_cash_data():
    payload = {'cash': {str(uid): amount for uid, amount in user_cash.items()}, 'debt': {str(uid): amount for uid, amount in user_debt.items()}, 'tax_evasion_debt': {str(uid): value for uid, value in tax_evasion_debt.items()}, 'tax_evasion_count': {str(uid): count for uid, count in tax_evasion_count.items()}, 'last_beg': {str(uid): ts for uid, ts in last_beg.items()}, 'last_work': {str(uid): ts for uid, ts in last_work.items()}, 'last_pray': {str(uid): ts for uid, ts in last_pray.items()}, 'last_loan': {str(uid): ts for uid, ts in last_loan.items()}, 'last_debt_penalty': {str(uid): ts for uid, ts in last_debt_penalty.items()}, 'last_tax': {str(uid): ts for uid, ts in last_tax.items()}, 'bot_stats': bot_stats, 'channel_id': CHANNEL_ID, 'server_wide_mode': SERVER_WIDE_MODE, 'excluded_channel_ids': list(EXCLUDED_CHANNEL_IDS)}
    return await atomic_save_json(CASH_FILE, payload, cash_file_lock, 'cash data')

async def prune_corpus_file(max_lines=MAX_CORPUS_LINES):
    if not os.path.exists(TEXT_FILE):
        return 0
    kept = deque(maxlen=max_lines)
    async with aiofiles.open(TEXT_FILE, 'r', encoding='utf-8') as f:
        async for line in f:
            stripped = line.rstrip('\n')
            if stripped:
                kept.append(stripped)
    async with aiofiles.open(TEXT_FILE, 'w', encoding='utf-8') as f:
        if kept:
            await f.write('\n'.join(kept) + '\n')
    return len(kept)

def get_remaining_cooldown(last_used_ts, cooldown_seconds):
    now = int(time.time())
    elapsed = now - int(last_used_ts)
    remaining = cooldown_seconds - elapsed
    return max(0, remaining)

def fmt_seconds(seconds):
    minutes = seconds // 60
    secs = seconds % 60
    if minutes > 0:
        return f'{minutes}m {secs}s'
    return f'{secs}s'

def tax_rate_for_balance(balance):
    """Marginal (top) rate for display purposes -- e.g. 'you're in the 10% bracket'."""
    for threshold, rate in TAX_BRACKETS:
        if balance >= threshold:
            return rate
    return 0.0

def tax_amount_for_balance(balance):
    """
    Progressive tax: each bracket's rate only applies to the slice of balance
    that falls within it, so crossing a threshold can never leave you with
    less after-tax cash than staying just under it.
    """
    if balance <= 0:
        return 0
    ordered = sorted(TAX_BRACKETS, key=lambda pair: pair[0])
    total_tax = 0.0
    for i, (threshold, rate) in enumerate(ordered):
        if balance <= threshold:
            continue
        upper = ordered[i + 1][0] if i + 1 < len(ordered) else None
        slice_top = balance if upper is None else min(balance, upper)
        slice_amount = slice_top - threshold
        if slice_amount > 0:
            total_tax += slice_amount * rate
    return int(total_tax)

async def apply_tax_if_due(uid, member=None):
    uid = int(uid)
    tax_amount, rate, remaining = get_tax_due(uid)
    if remaining > 0:
        return (0, 0.0)
    last_tax[uid] = int(time.time())
    if tax_amount > 0:
        await modify_cash(uid, -tax_amount, member)
    else:
        await save_cash_data()
    return (tax_amount, rate)

async def apply_debt_penalty_if_due(uid, member=None):
    uid = int(uid)
    debt = get_debt(uid)
    if debt <= 0:
        return (0, 0, 0)
    now = int(time.time())
    anchor = last_debt_penalty.get(uid, now)
    elapsed = now - anchor
    ticks = elapsed // DEBT_PENALTY_INTERVAL_SECONDS
    if ticks <= 0:
        return (0, 0, 0)
    async with get_cash_lock(uid):
        balance = get_cash(uid)
        total_cash_fee = 0
        total_debt_added = 0
        for _ in range(int(ticks)):
            debt_growth = max(1, int(debt * DEBT_PENALTY_DEBT_RATE))
            cash_fee = min(DEBT_PENALTY_CASH_FEE, balance)
            debt += debt_growth
            balance -= cash_fee
            total_debt_added += debt_growth
            total_cash_fee += cash_fee
        user_debt[uid] = max(0, debt)
        last_debt_penalty[uid] = anchor + int(ticks) * DEBT_PENALTY_INTERVAL_SECONDS
        await set_cash(uid, balance, member)
    return (total_cash_fee, total_debt_added, int(ticks))

def clear_tax_evasion_flag(uid):
    uid = int(uid)
    if user_debt.get(uid, 0) <= 0:
        tax_evasion_debt.pop(uid, None)

def has_tax_evasion_debt(uid):
    uid = int(uid)
    return bool(tax_evasion_debt.get(uid, False) and get_debt(uid) > 0)

async def terminal_send(channel, content, label='message'):
    """Send to Discord from the terminal and print whether it actually went through."""
    try:
        await channel.send(content)
        preview = content if len(content) <= 60 else content[:57] + '...'
        print(f"[TERMINAL] sent {label} to #{getattr(channel, 'name', channel.id)}: {preview}")
        return True
    except discord.HTTPException as exc:
        print(f'[TERMINAL] FAILED to send {label}: {exc}')
        return False

def resolve_terminal_user(channel, query):
    """Resolve a terminal-supplied user reference: raw ID, or a
    case-insensitive substring match against display name/username."""
    query = query.strip()
    if query.isdigit():
        if channel.guild is not None:
            member = channel.guild.get_member(int(query))
            if member is not None:
                return member
        return int(query)
    if channel.guild is None:
        return None
    query_lower = query.lower()
    for member in channel.guild.members:
        if query_lower in member.display_name.lower() or query_lower in member.name.lower():
            return member
    return None

def terminal_uid(user):
    return user.id if hasattr(user, 'id') else int(user)

def terminal_label(user):
    return user.mention if isinstance(user, discord.Member) else f'user {terminal_uid(user)}'
TERMINAL_HELP = "[TERMINAL] Commands:\n  /help                          show this list\n  /force                         force a phrase reply now\n  /say <msg>                     send raw text to the channel\n  /channel [id]                  show or switch the active channel\n  /stats                         print bot_stats\n  /users                         list everyone with a known cash balance\n  /cash <user>                   show a user's cash + debt\n  /setcash <user> <amount>       set a user's cash\n  /addcash <user> <amount>       add to a user's cash\n  /takecash <user> <amount>      subtract from a user's cash\n  /setdebt <user> <amount>       set a user's debt\n  /resetuser <user>              reset a user's cash/debt/cooldowns\n  /inventory <user>              show a user's inventory\n  /giveitem <user> <item> [qty]  give shop items to a user\n  /sleep                         force the bot to sleep\n  /wake                          force the bot awake\n  /mode global                   switch markov mode to global\n  /mode track <user>             switch markov mode to track a user\n  /nuke confirm                  purge + timeout everyone in the channel\n  /save                          force-save cash/inventory/corpus to disk\n  /reload                        reload cash/inventory/corpus from disk\n  /shutdown                      gracefully close the bot\n  anything else                  sent as raw text to the channel"

async def terminal_input_loop():
    global CHANNEL_ID, mode, track_target, sleep_override, bot_is_asleep
    await bot.wait_until_ready()
    channel = bot.get_channel(CHANNEL_ID)
    if channel is None:
        print('[TERMINAL] Channel not found')
        return
    loop = asyncio.get_running_loop()
    print(TERMINAL_HELP)
    while True:
        raw = await loop.run_in_executor(None, input)
        raw = raw.strip()
        if not raw:
            continue
        parts = raw.split()
        cmd = parts[0].lower()
        args = parts[1:]
        if cmd == '/help':
            print(TERMINAL_HELP)
            continue
        if cmd == '/force':
            result = await send_phrase_reply(channel)
            if result is None:
                print('[TERMINAL] roll produced no reply (silence/duplicate/empty pool)')
            else:
                preview = result if len(result) <= 60 else result[:57] + '...'
                print(f'[TERMINAL] sent: {preview}')
            continue
        if cmd == '/say':
            if len(parts) < 2:
                print('[TERMINAL] usage: /say <msg>')
                continue
            await terminal_send(channel, raw[len(cmd) + 1:], label='say')
            continue
        if cmd == '/channel':
            if not args:
                print(f"[TERMINAL] active channel: {channel.id} (#{getattr(channel, 'name', '?')})")
                continue
            try:
                new_id = int(args[0])
            except ValueError:
                print('[TERMINAL] channel id must be a number')
                continue
            new_channel = bot.get_channel(new_id)
            if new_channel is None:
                print(f'[TERMINAL] no channel with id {new_id} found in cache')
                continue
            channel = new_channel
            CHANNEL_ID = new_id
            print(f"[TERMINAL] active channel switched to {new_id} (#{getattr(channel, 'name', '?')})")
            continue
        if cmd == '/stats':
            for key, value in bot_stats.items():
                print(f'  {key}: {value}')
            continue
        if cmd == '/users':
            if not user_cash:
                print('[TERMINAL] no users tracked yet')
                continue
            for uid, amount in sorted(user_cash.items(), key=lambda p: p[1], reverse=True):
                debt = get_debt(uid)
                print(f'  {uid}: ${amount}' + (f' (debt ${debt})' if debt else ''))
            continue
        if cmd == '/cash':
            if not args:
                print('[TERMINAL] usage: /cash <user>')
                continue
            user = resolve_terminal_user(channel, ' '.join(args))
            if user is None:
                print('[TERMINAL] user not found')
                continue
            uid = terminal_uid(user)
            print(f'[TERMINAL] {terminal_label(user)}: cash ${get_cash(uid)}, debt ${get_debt(uid)}')
            continue
        if cmd in ('/setcash', '/addcash', '/takecash'):
            if len(args) < 2:
                print(f'[TERMINAL] usage: {cmd} <user> <amount>')
                continue
            user = resolve_terminal_user(channel, args[0])
            if user is None:
                print('[TERMINAL] user not found')
                continue
            try:
                amount = int(args[1])
            except ValueError:
                print('[TERMINAL] amount must be a number')
                continue
            uid = terminal_uid(user)
            member = user if isinstance(user, discord.Member) else None
            if cmd == '/setcash':
                await set_cash_locked(uid, amount, member, force_nick=True)
            elif cmd == '/addcash':
                await modify_cash(uid, amount, member, force_nick=True)
            else:
                await modify_cash(uid, -amount, member, force_nick=True)
            print(f'[TERMINAL] {terminal_label(user)} cash is now ${get_cash(uid)}')
            continue
        if cmd == '/setdebt':
            if len(args) < 2:
                print('[TERMINAL] usage: /setdebt <user> <amount>')
                continue
            user = resolve_terminal_user(channel, args[0])
            if user is None:
                print('[TERMINAL] user not found')
                continue
            try:
                amount = max(0, int(args[1]))
            except ValueError:
                print('[TERMINAL] amount must be a number')
                continue
            uid = terminal_uid(user)
            user_debt[uid] = amount
            await save_cash_data()
            print(f'[TERMINAL] {terminal_label(user)} debt is now ${amount}')
            continue
        if cmd == '/resetuser':
            if not args:
                print('[TERMINAL] usage: /resetuser <user>')
                continue
            user = resolve_terminal_user(channel, ' '.join(args))
            if user is None:
                print('[TERMINAL] user not found')
                continue
            uid = terminal_uid(user)
            clear_user_state(uid)
            if isinstance(user, discord.Member):
                await update_cash_nick(user, STARTING_CASH, force=True)
            await save_cash_data()
            await save_inventory_data()
            print(f'[TERMINAL] reset {terminal_label(user)}')
            continue
        if cmd == '/inventory':
            if not args:
                print('[TERMINAL] usage: /inventory <user>')
                continue
            user = resolve_terminal_user(channel, ' '.join(args))
            if user is None:
                print('[TERMINAL] user not found')
                continue
            uid = terminal_uid(user)
            inv = get_inventory(uid)
            if not inv:
                print(f'[TERMINAL] {terminal_label(user)} has nothing')
                continue
            for item_id, qty in inv.items():
                name = SHOP_ITEMS.get(item_id, {}).get('name', item_id)
                print(f'  {name} x{qty}')
            continue
        if cmd == '/giveitem':
            if len(args) < 2:
                print('[TERMINAL] usage: /giveitem <user> <item> [qty]')
                continue
            user = resolve_terminal_user(channel, args[0])
            if user is None:
                print('[TERMINAL] user not found')
                continue
            item_id = find_shop_item(args[1])
            if item_id is None:
                print(f"[TERMINAL] no item called '{args[1]}'")
                continue
            qty = 1
            if len(args) > 2:
                try:
                    qty = int(args[2])
                except ValueError:
                    print('[TERMINAL] qty must be a number')
                    continue
            uid = terminal_uid(user)
            add_item(uid, item_id, qty)
            await save_inventory_data()
            print(f"[TERMINAL] gave {qty}x {SHOP_ITEMS[item_id]['name']} to {terminal_label(user)}")
            continue
        if cmd == '/sleep':
            sleep_override = True
            bot_is_asleep = True
            print('[TERMINAL] bot is now asleep')
            continue
        if cmd == '/wake':
            sleep_override = None
            bot_is_asleep = False
            print('[TERMINAL] bot is now awake')
            continue
        if cmd == '/mode':
            if not args:
                print(f'[TERMINAL] current mode: {mode}' + (f' (tracking {track_target})' if track_target else ''))
                continue
            if args[0] == 'global':
                mode = 'global'
                track_target = None
                print('[TERMINAL] mode set to global')
                continue
            if args[0] == 'track':
                if len(args) < 2:
                    print('[TERMINAL] usage: /mode track <user>')
                    continue
                user = resolve_terminal_user(channel, ' '.join(args[1:]))
                if user is None:
                    print('[TERMINAL] user not found')
                    continue
                mode = 'track'
                track_target = terminal_uid(user)
                print(f'[TERMINAL] mode set to track {terminal_label(user)}')
                continue
            print('[TERMINAL] usage: /mode global | /mode track <user>')
            continue
        if cmd == '/nuke':
            if args[:1] != ['confirm']:
                print("[TERMINAL] this purges the channel and times out everyone who posted. run '/nuke confirm' to proceed.")
                continue
            print('[TERMINAL] nuking...')
            summary = await perform_nuke(channel)
            await terminal_send(channel, summary, label='nuke summary')
            continue
        if cmd == '/save':
            ok_cash = await save_cash_data()
            ok_inv = await save_inventory_data()
            print(f"[TERMINAL] save: cash={('ok' if ok_cash else 'FAILED')} inventory={('ok' if ok_inv else 'FAILED')}")
            continue
        if cmd == '/reload':
            try:
                await load_cash_data(allow_empty=False)
                await load_inventory_data()
                await load_corpus()
                print('[TERMINAL] reloaded cash/inventory/corpus from disk')
            except (OSError, ValueError) as exc:
                print(f'[TERMINAL] reload refused: {exc}')
            continue
        if cmd == '/shutdown':
            await graceful_shutdown()
            return
        await terminal_send(channel, raw, label='raw text')

async def get_recent_human_members(channel, max_messages=60):
    members = {}
    async for msg in channel.history(limit=max_messages):
        author = msg.author
        if getattr(author, 'bot', False):
            continue
        if bot_user_id is not None and author.id == bot_user_id:
            continue
        members[author.id] = author
    return list(members.values())
AUTOSAVE_INTERVAL_SECONDS = 300

async def autosave_loop():
    """Safety-net save independent of action-triggered saves, in case
    something throws between a state change and its explicit save call."""
    await bot.wait_until_ready()
    while True:
        await asyncio.sleep(AUTOSAVE_INTERVAL_SECONDS)
        ok = await save_cash_data()
        ok_inv = await save_inventory_data()
        debug(f"Autosave cash={('ok' if ok else 'FAILED')} inventory={('ok' if ok_inv else 'FAILED')}")

async def graceful_shutdown():
    """Save persistent state, stop background loops, and close Discord."""
    global shutdown_started
    if shutdown_started:
        return
    shutdown_started = True
    print('[SHUTDOWN] Saving all data...')
    results = await asyncio.gather(save_cash_data(), save_inventory_data(), save_seen_gif_keys(), return_exceptions=True)
    for result in results:
        if isinstance(result, Exception):
            print(f'[SHUTDOWN] Save failed: {result!r}')
    current = asyncio.current_task()
    pending = []
    for task in background_tasks:
        if task is not current and (not task.done()):
            task.cancel()
            pending.append(task)
    if pending:
        await asyncio.gather(*pending, return_exceptions=True)
    print('[SHUTDOWN] Data saved. Closing Discord connection...')
    await bot.close()

async def bot_economy_loop():
    await bot.wait_until_ready()
    while True:
        await asyncio.sleep(random.randint(BOT_AUTO_MIN_DELAY, BOT_AUTO_MAX_DELAY))
        if is_bedtime():
            continue
        if not BOT_AUTO_ECONOMY_ENABLED:
            continue
        if random.random() > BOT_AUTO_TRIGGER_CHANCE:
            continue
        if bot_user_id is None:
            continue
        channel = bot.get_channel(CHANNEL_ID_DEFAULT)
        if channel is None:
            continue
        guild = getattr(channel, 'guild', None)
        bot_member = guild.get_member(bot_user_id) if guild is not None else None
        available_actions = []
        recent_targets = []
        if get_remaining_cooldown(last_beg.get(bot_user_id, 0), BEG_COOLDOWN) == 0:
            available_actions.append('beg')
        if get_remaining_cooldown(last_work.get(bot_user_id, 0), WORK_COOLDOWN) == 0:
            available_actions.append('work')
        if get_bot_cash() > 0:
            available_actions.append('gamble')
        if get_bot_cash() >= BOT_MIN_BALANCE_FOR_SOCIAL and random.random() < BOT_SOCIAL_ACTION_CHANCE:
            recent_targets = await get_recent_human_members(channel)
            if recent_targets:
                available_actions.append('give')
                available_actions.append('steal')
        if not available_actions:
            continue
        action = random.choice(available_actions)
        if action == 'beg':
            reward = random.randint(BEG_MIN, BEG_MAX)
            last_beg[bot_user_id] = int(time.time())
            await modify_cash(bot_user_id, reward, bot_member)
            await channel.send(f'*begs for change* got ${reward}. bot cash: ${get_bot_cash()}')
            continue
        if action == 'work':
            reward = random.randint(WORK_MIN, WORK_MAX)
            last_work[bot_user_id] = int(time.time())
            await modify_cash(bot_user_id, reward, bot_member)
            await channel.send(f'*works a shift* earned ${reward}. bot cash: ${get_bot_cash()}')
            continue
        if action == 'give':
            if not recent_targets:
                continue
            target = random.choice(recent_targets)
            balance = get_bot_cash()
            if balance <= 0:
                continue
            give_amount = min(balance, random.randint(BOT_GIVE_MIN, BOT_GIVE_MAX))
            if give_amount <= 0:
                continue
            await modify_cash(bot_user_id, -give_amount, bot_member)
            await modify_cash(target.id, give_amount, target if isinstance(target, discord.Member) else None)
            bot_stats['given'] += give_amount
            await save_cash_data()
            await channel.send(f'bot gave ${give_amount} to {target.mention}. balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}')
            continue
        if action == 'steal':
            if not recent_targets:
                continue
            target = random.choice(recent_targets)
            target_balance = get_cash(target.id)
            thief_balance = get_bot_cash()
            if target_balance <= 0:
                continue
            steal_amount = min(target_balance, random.randint(BOT_STEAL_MIN, BOT_STEAL_MAX))
            if steal_amount <= 0:
                continue
            success = random.random() < STEAL_SUCCESS_CHANCE
            if success:
                bot_stats['steal_success'] += 1
                await modify_cash(bot_user_id, steal_amount, bot_member)
                await modify_cash(target.id, -steal_amount, target if isinstance(target, discord.Member) else None)
                await save_cash_data()
                await channel.send(f'bot steal success: took ${steal_amount} from {target.mention}. balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}')
                continue
            penalty = max(1, int(steal_amount * STEAL_FAIL_PENALTY_RATE))
            penalty = min(penalty, thief_balance)
            bot_stats['steal_fail'] += 1
            if penalty > 0:
                await modify_cash(bot_user_id, -penalty, bot_member)
                await modify_cash(target.id, penalty, target if isinstance(target, discord.Member) else None)
                await save_cash_data()
                await channel.send(f'bot steal failed: paid ${penalty} to {target.mention}. balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}')
            else:
                await save_cash_data()
                await channel.send('bot steal failed, but had no money for penalty')
            continue
        balance = get_bot_cash()
        if balance <= 0:
            continue
        bet = min(balance, random.randint(BOT_GAMBLE_BET_MIN, BOT_GAMBLE_BET_MAX))
        if bet <= 0:
            continue
        won = random.random() < GAMBLE_WIN_CHANCE
        await modify_cash(bot_user_id, bet if won else -bet, bot_member)
        new_balance = get_bot_cash()
        if won:
            bot_stats['gamble_wins'] += 1
            await save_cash_data()
            await channel.send(f'bot gambled ${bet} and won. bot cash: ${new_balance}')
        else:
            bot_stats['gamble_losses'] += 1
            await save_cash_data()
            await channel.send(f'bot gambled ${bet} and lost. bot cash: ${new_balance}')

def learn_reactions(text):
    words = text.split()
    if len(words) < 3:
        return
    reaction_starts.append(words[0])
    reaction_ends.append(words[-1])
    reaction_middles.append(' '.join(words[1:-1]))
    if len(reaction_starts) > MAX_REACTIONS:
        reaction_starts.pop(0)
        reaction_middles.pop(0)
        reaction_ends.pop(0)
    debug('Learned reaction pattern')

def generate_learned_reaction():
    if not reaction_starts or not reaction_ends:
        debug('Reaction generation failed: insufficient data')
        return None
    start = random.choice(reaction_starts)
    end = random.choice(reaction_ends)
    middle = ''
    if reaction_middles and random.random() < 0.7:
        middle = ' ' + random.choice(reaction_middles)
    return f'{start}{middle} {end}'.strip()

async def append_corpus_line(uid, text, is_quote=False):
    global corpus_line_count
    payload = text.strip()
    if not payload:
        return
    if is_quote:
        payload = f'{CORPUS_QUOTE_PREFIX}{payload}'
    line = f'{int(uid)}::{payload}\n'
    try:
        async with aiofiles.open(TEXT_FILE, 'a', encoding='utf-8') as f:
            await f.write(line)
        corpus_line_count += 1
        if corpus_line_count > MAX_CORPUS_LINES:
            corpus_line_count = await prune_corpus_file()
    except OSError as exc:
        debug(f'Corpus append failed, pruning and retrying: {exc}')
        corpus_line_count = await prune_corpus_file()
        try:
            async with aiofiles.open(TEXT_FILE, 'a', encoding='utf-8') as f:
                await f.write(line)
            corpus_line_count += 1
        except OSError as retry_exc:
            debug(f'Corpus append still failed after prune: {retry_exc}')
            return

async def load_corpus():
    global corpus_line_count
    if not os.path.exists(TEXT_FILE):
        return
    corpus_line_count = 0
    async with aiofiles.open(TEXT_FILE, 'r', encoding='utf-8') as f:
        async for line in f:
            corpus_line_count += 1
            line = line.strip()
            if '::' not in line:
                continue
            uid, phrase = line.split('::', 1)
            is_quote = phrase.startswith(CORPUS_QUOTE_PREFIX)
            if is_quote:
                phrase = phrase[len(CORPUS_QUOTE_PREFIX):].strip()
            try:
                uid = int(uid)
            except ValueError:
                continue
            if is_quote:
                user_quotes.setdefault(uid, []).append(phrase)
                continue
            if not is_valid_phrase(phrase):
                continue
            user_pools.setdefault(uid, []).append(phrase)
            user_full_lines.setdefault(uid, []).append(phrase)
            if len(user_full_lines[uid]) > MAX_TRACK_LINES:
                user_full_lines[uid].pop(0)
    debug('Corpus loaded')
    if corpus_line_count > MAX_CORPUS_LINES:
        corpus_line_count = await prune_corpus_file()

async def send_phrase_reply(channel):
    if random.random() < SILENCE_CHANCE:
        debug('Silence roll triggered')
        return None
    if random.random() < 0.25:
        possible_commands = ['!beg', '!work', '!pray', '!gamble all']
        recent_targets = await get_recent_human_members(channel)
        if recent_targets:
            steal_target = random.choice(recent_targets)
            possible_commands.append(f'!steal {steal_target.mention} all')
        chosen = random.choice(possible_commands)
        debug(f'Bot using command: {chosen}')
        await channel.send(chosen)
        return chosen
    if mode == 'track':
        source_pool = user_full_lines.get(track_target, [])[-MAX_RECENT_PHRASES:]
        if not source_pool:
            source_pool = user_pools.get(track_target, [])[-MAX_RECENT_PHRASES:]
        debug(f'Using TRACK full-line pool ({len(source_pool)})')
        if not source_pool:
            debug('No tracked full lines available')
            return None
        sentence = random.choice(source_pool)
        debug('Reply type: full line echo')
    else:
        source_pool = []
        for phrases in user_pools.values():
            source_pool.extend(phrases[-MAX_RECENT_PHRASES:])
        debug(f'Using GLOBAL pool ({len(source_pool)})')
        if not source_pool:
            sentence = random.choice(FALLBACKS)
            debug('Using fallback')
        else:
            roll = random.random()
            debug(f'Reply roll: {roll:.2f}')
            if roll < 0.25:
                sentence = random.choice(source_pool)
                debug('Reply type: direct echo')
            elif roll < 0.5:
                sentence = generate_learned_reaction() or random.choice(source_pool)
                debug('Reply type: learned reaction')
            elif roll < 0.8:
                count = random.randint(2, MAX_REPLY_PHRASES)
                parts = random.sample(source_pool, min(count, len(source_pool)))
                sentence = ' '.join(parts)
                debug(f'Reply type: mash ({count})')
            elif len(source_pool) >= 2:
                a, b = random.sample(source_pool, 2)
                sentence = remix_phrase(a, b)
                debug('Reply type: remix')
            else:
                sentence = source_pool[0]
    if sentence in recent_sentences:
        debug('Sentence rejected (recent duplicate)')
        return None
    recent_sentences.append(sentence)
    if len(recent_sentences) > MAX_RECENT_SENTENCES:
        recent_sentences.pop(0)
    debug(f'Sending: {sentence}')
    bot_stats['replies_sent'] += 1
    await save_cash_data()
    await channel.send(sentence)
    return sentence

@bot.event
async def on_command_error(ctx, error):
    if not is_active_channel(ctx.channel):
        return
    if isinstance(error, commands.CommandNotFound):
        return
    if isinstance(error, commands.CheckFailure):
        await ctx.send('not allowed')
        return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.send(f"that's on cooldown, try again in {fmt_seconds(int(error.retry_after))}")
        return
    if isinstance(error, commands.MemberNotFound):
        await ctx.send(f"couldn't find a member matching '{error.argument}'")
        return
    if isinstance(error, commands.MissingRequiredArgument):
        await ctx.send(f'missing an argument: {error.param.name}. check the command usage.')
        return
    if isinstance(error, commands.BadArgument):
        await ctx.send("that argument doesn't look right, double check the command usage.")
        return
    debug(f'Unhandled command error in {ctx.command}: {error!r}')
    await ctx.send('something went wrong running that command.')

@bot.event
async def on_ready():
    global bot_user_id, tasks_started
    if tasks_started:
        print(f'[LINK] Discord connection restored as {bot.user}')
        return
    boot_banner()
    boot_status('PYTHON RUNTIME', sys.version.split()[0])
    await load_corpus()
    boot_status('LANGUAGE CORPUS', f'{corpus_line_count} LINES')
    cash_loaded = await load_cash_data()
    boot_status('ECONOMY DATABASE', f'{len(user_cash)} ACCOUNTS' if cash_loaded else 'NEW DATABASE')
    await load_inventory_data()
    boot_status('INVENTORY DATABASE', f'{len(user_inventory)} ACCOUNTS')
    await load_seen_gif_keys()
    boot_status('GIF MEMORY', f'{len(seen_gif_keys)} SIGNATURES')
    bot_user_id = bot.user.id
    get_cash(bot_user_id)
    boot_status('DISCORD LINK', str(bot.user))
    try:
        synced = await bot.tree.sync()
        boot_status('SLASH COMMANDS', f'{len(synced)} SYNCED')
    except Exception as e:
        boot_status('SLASH COMMANDS', 'SYNC FAILED')
        debug(f'Slash command sync failed: {e}')
    boot_status('PREFIX COMMANDS', f'{len(bot.commands)} REGISTERED')
    tasks_started = True
    if os.getenv('ENABLE_TERMINAL_INPUT', 'false').lower() == 'true':
        background_tasks.append(asyncio.create_task(terminal_input_loop()))
        boot_status('TERMINAL CONTROL', 'ENABLED')
    else:
        boot_status('TERMINAL CONTROL', 'DISABLED')
    background_tasks.append(asyncio.create_task(bot_economy_loop()))
    background_tasks.append(asyncio.create_task(autosave_loop()))
    print('[READY] ALL SYSTEMS NOMINAL // JACHLAM IS ONLINE')
GIF_URL_PATTERN = re.compile('(https?://\\S+\\.(?:gif|gifv)\\S*|https?://(?:media\\.)?tenor\\.com/\\S+|https?://(?:media\\.)?giphy\\.com/\\S+|https?://(?:www\\.)?klipy\\.com/gifs/\\S+)', re.IGNORECASE)

def _extract_gif_keys(message):
    keys = []
    for attachment in message.attachments:
        name = (attachment.filename or '').lower()
        if name.endswith(('.gif', '.gifv', '.webp', '.mp4')) or 'gif' in (attachment.content_type or ''):
            keys.append(f'attach:{attachment.filename}:{attachment.size}')
    for match in GIF_URL_PATTERN.findall(message.content or ''):
        keys.append(f"url:{match.strip().split('?')[0].rstrip('/')}")
    for sticker in message.stickers:
        keys.append(f'sticker:{sticker.id}')
    return keys

async def check_gif_repeat(message):
    """If the configured user reposts a gif that's already been seen in the
    channel, timeout them for GIF_REPEAT_TIMEOUT_DAYS. Native Discord timeout
    (reversible, capped at 28 days) rather than a ban -- this is a joke
    feature and shouldn't permanently remove anyone over a false positive."""
    if ORION_USER_ID is None:
        return
    keys = _extract_gif_keys(message)
    if not keys:
        return
    if message.author.id != ORION_USER_ID:
        seen_gif_keys.update(keys)
        return
    repeats = [k for k in keys if k in seen_gif_keys]
    seen_gif_keys.update(keys)
    if not repeats:
        return
    member = message.author
    if not isinstance(member, discord.Member):
        return
    try:
        debug(f'Bot top role: {member.guild.me.top_role} ({member.guild.me.top_role.position})')
        debug(f'Target top role: {member.top_role} ({member.top_role.position})')
        debug(f'Bot can moderate target: {member.guild.me.top_role > member.top_role}')
        debug(f'Bot has moderate_members: {member.guild.me.guild_permissions.moderate_members}')
        debug(f'Target is owner: {member.guild.owner_id == member.id}')
        await member.timeout(timedelta(days=GIF_REPEAT_TIMEOUT_DAYS), reason="Reposted a gif that's already been used")
        await message.channel.send(f"{member.mention} reposted a gif that's already been used. timed out for {GIF_REPEAT_TIMEOUT_DAYS} days.")
    except discord.HTTPException as exc:
        debug(f'Failed to timeout {member.display_name} for gif repeat: {exc}')

@bot.event
async def on_message(message):
    global message_counter, messages_per_reply
    if not is_active_channel(message.channel):
        return
    if message.author.bot and message.author.id != bot.user.id:
        return
    is_self_message = message.author.id == bot.user.id
    global bot_is_asleep
    raw_content_peek = message.content.strip()
    command_peek = raw_content_peek.split(maxsplit=1)[0].lower() if raw_content_peek else ''
    if command_peek in {'!sleep', '!wake'}:
        await bot.process_commands(message)
        return
    if is_bedtime():
        if not bot_is_asleep:
            bot_is_asleep = True
            for guild in bot.guilds:
                for active_channel in get_active_text_channels(guild):
                    try:
                        await active_channel.send('going to bed, back at 7am')
                    except discord.HTTPException:
                        pass
        return
    else:
        bot_is_asleep = False
    if not is_self_message:
        await check_gif_repeat(message)
    raw_content = message.content.strip()
    content = raw_content.lower()
    uid = message.author.id
    command_name = raw_content.split(maxsplit=1)[0].lower() if raw_content else ''
    skip_auto_tax = command_name in {'!evade', '!taxevade'}
    if not is_self_message:
        get_cash(uid)
        debt_fee, debt_growth, debt_ticks = await apply_debt_penalty_if_due(uid, message.author)
        taxed, rate = (0, 0.0) if skip_auto_tax else await apply_tax_if_due(uid, message.author)
        bot_stats['messages_seen'] += 1
        if debt_ticks > 0:
            await message.channel.send(f'{message.author.mention} overdue loan penalty x{debt_ticks}: -${debt_fee} cash, +${debt_growth} debt. cash: ${get_cash(uid)} | debt: ${get_debt(uid)}')
        if taxed > 0:
            if bot_user_id is not None:
                await modify_cash(bot_user_id, taxed)
                bot_stats['tax_collected'] += taxed
            await message.channel.send(f'{message.author.mention} paid ${taxed} tax ({int(rate * 100)}%). new balance: ${get_cash(uid)}')
    debug(f'Message from {message.author.display_name}: {content}')
    debug(f'Mode: {mode}')
    if not is_self_message:
        if mode == 'track' and uid == track_target and raw_content and (not raw_content.startswith('!')):
            user_full_lines.setdefault(uid, []).append(raw_content)
            if len(user_full_lines[uid]) > MAX_TRACK_LINES:
                user_full_lines[uid].pop(0)
        if is_valid_phrase(content):
            debug('Phrase accepted')
            learn_reactions(content)
            if mode == 'global' or (mode == 'track' and uid == track_target):
                user_pools.setdefault(uid, []).append(content)
                if len(user_pools[uid]) > MAX_PHRASES:
                    user_pools[uid].pop(0)
                await append_corpus_line(uid, content, is_quote=False)
        else:
            debug('Phrase rejected')
        if raw_content and (not raw_content.startswith('!')):
            message_counter += 1
            debug(f'Message counter: {message_counter}/{messages_per_reply}')
            if message_counter >= messages_per_reply:
                message_counter = 0
                messages_per_reply = random.randint(1, 5)
                debug(f'Trigger reply, next in {messages_per_reply}')
                await send_phrase_reply(message.channel)
    await bot.process_commands(message)

@bot.command(name='resync')
@commands.has_permissions(administrator=True)
async def resync(ctx):
    if not is_active_channel(ctx.channel):
        return
    await ctx.send("\U0001f504 resyncing Jachlam's financial records...")
    try:
        await load_cash_data(allow_empty=False)
        await load_inventory_data()
        updated = 0
        failed = 0
        for guild in bot.guilds:
            for member in guild.members:
                try:
                    if member.id not in user_cash:
                        continue
                    await update_cash_nick(member, get_display_cash(member.id), force=True)
                    updated += 1
                except discord.HTTPException as exc:
                    failed += 1
                    debug(f'Failed to resync nickname for {member.display_name}: {exc}')
        await ctx.send(f'\u2705 **Resync complete.**\n\U0001f4b0 Cash records reloaded.\n\U0001f3a8 Updated **{updated}** nicknames.\n\u274c Failed: **{failed}**.')
    except Exception as exc:
        debug(f'Resync failed: {exc}')
        await ctx.send('\u274c resync failed. check the console for details.')

@bot.command(name='audit')
@commands.has_permissions(administrator=True)
async def audit(ctx, member: discord.Member=None):
    if not is_active_channel(ctx.channel):
        return
    if member is None:
        member = ctx.author
    uid = member.id
    cash = get_cash(uid)
    debt = get_debt(uid)
    evades = tax_evasion_count.get(uid, 0)
    tax_amount, rate, remaining = get_tax_due(uid, ignore_timer=True)
    fine = 250 * evades
    total_bill = tax_amount + fine
    collected = 0
    debt_added = 0
    if evades > 0:
        collected = min(cash, total_bill)
        debt_added = total_bill - collected
        await set_cash_locked(uid, cash - collected, member, force_nick=True)
        if debt_added:
            user_debt[uid] = get_debt(uid) + debt_added
            tax_evasion_debt[uid] = True
        tax_evasion_count[uid] = 0
        last_tax[uid] = int(time.time())
        await save_cash_data()
        status = '\u26a0\ufe0f IRREGULARITIES DETECTED \u2014 PENALTY APPLIED'
        result = f'Tax Recovered: **${tax_amount:,}**\nEvasion Fine: **${fine:,}**\nTaken From Cash: **${collected:,}**\nAdded To Debt: **${debt_added:,}**'
    else:
        status = '\u2705 NO IRREGULARITIES DETECTED'
        result = 'No enforcement action was required.'
    embed = discord.Embed(title='\U0001f4d1 OFFICIAL FINANCIAL AUDIT', description=f'**SUBJECT:** {member.mention}\n**IDENTIFICATION:** `{member.id}`\n**CLASSIFICATION:** CONFIDENTIAL', color=discord.Color.dark_red())
    embed.add_field(name='FINANCIAL RECORD BEFORE AUDIT', value=f'Cash Holdings: **${cash:,}**\nOutstanding Debt: **${debt:,}**', inline=False)
    embed.add_field(name='TAX ASSESSMENT', value=f'Current Assessment: **${tax_amount:,}**\nApplicable Rate: **{rate * 100:.1f}%**\nRecorded Tax Evasions: **{evades}**', inline=False)
    embed.add_field(name='AUDIT RESULT', value=f'Status: **{status}**\n\n{result}', inline=False)
    embed.add_field(name='UPDATED FINANCIAL RECORD', value=f'Cash Holdings: **${get_cash(uid):,}**\nOutstanding Debt: **${get_debt(uid):,}**', inline=False)
    embed.set_footer(text='OFFICIAL RECORD \u2022 DEPARTMENT OF JACHLAM AFFAIRS')
    await ctx.send(embed=embed)

@bot.command(name='appeal')
async def appeal(ctx):
    if not is_active_channel(ctx.channel):
        return
    await ctx.send(f'\U0001f4c4 **APPEAL DENIED**\nApplicant: {ctx.author.mention}\nDecision: **NO**\nReason: **lol no**')

@audit.error
async def audit_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send('\U0001f6ab **ACCESS DENIED**\nAdministrator authorization is required to access this record.')
    else:
        debug(f'Unhandled audit error: {error}')
        await ctx.send('\u274c something went wrong running that command.')

@bot.command(name='expunge')
@commands.has_permissions(administrator=True)
async def expunge(ctx, member: discord.Member):
    try:
        await member.ban(reason=f'Expunged by {ctx.author}')
        await ctx.send(f'\u2554\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2557\n        **CLASSIFIED \u2014 EXPUNGEMENT NOTICE**\n\u255a\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u255d\n\n**DEPARTMENT OF JACHLAM AFFAIRS**\n**EXPUNGEMENT ORDER:** #{member.id}\n\n**SUBJECT:** {member.mention}\n**STATUS:** \u2612 EXPUNGED\n**THREAT LEVEL:** ADMINISTRATIVELY INCONVENIENT\n\nFollowing a review by the Department of Jachlam Affairs, the above subject has been determined to be **expungable**.\n\n\u2611 Ban approved\n\u2611 Subject removed from server\n\u2611 Records classified\n\u2611 Appeal request denied\n\n**NOTICE:** Any attempt to reintroduce the subject without proper authorization will be treated as an additional administrative violation.\n\n**\u2014 JACHLAM ADMINISTRATIVE CONTROL DIVISION \u2014**')
    except discord.Forbidden:
        await ctx.send('\U0001f6ab EXPUNGEMENT FAILED: insufficient permissions.')
    except discord.HTTPException as exc:
        debug(f'Failed to expunge {member.display_name}: {exc}')
        await ctx.send('\u26a0\ufe0f EXPUNGEMENT FAILED: an internal error occurred.')

@bot.command()
@commands.has_permissions(administrator=True)
async def rick(ctx):
    if is_active_channel(ctx.channel):
        debug('ricked')
        await ctx.send("We're no strangers to love\nYou know the rules and so do I\nA full commitment's what I'm thinking of\nYou wouldn't get this from any other guy\nI just wanna tell you how I'm feeling\nGotta make you understand Never gonna give you up\nNever gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye Never gonna tell a lie and hurt you We've known each other for so long your heart's been aching but you're too shy to say it Inside we both know what's been going on We know the game and we're gonna play it And if you ask me how I'm feeling Don't tell me you're too blind to see\nNever gonna give you up\nNever gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye\nNever gonna tell a lie and hurt you\nNever gonna give you up Never gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye Never gonna tell a lie and hurt you Never gonna give, never gonna give (Give you up)\nWe've known each other for so long your heart's been aching but you're too shy to say it Inside we both know what's been going on We know the game and we're gonna play it And if you ask me how I'm feeling Don't tell me you're too blind to see Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye Never gonna tell a lie and hurt you Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye Never gonna tell a lie and hurt you Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye")

@bot.command()
async def force(ctx):
    if is_active_channel(ctx.channel):
        debug('Force command used')
        await send_phrase_reply(ctx.channel)

@bot.command(name='assassinate')
async def assassinate(ctx, member: discord.Member):
    if not is_active_channel(ctx.channel):
        return
    attacker_id = ctx.author.id
    target_id = member.id
    privileged = is_money_admin(attacker_id)
    if attacker_id == target_id:
        await ctx.send("You can't assassinate yourself. Try therapy instead.")
        return
    if not privileged:
        can_use, remaining = can_use_assassinate(attacker_id)
        if not can_use:
            await ctx.send(f'Assassinate is on cooldown. Try again in {fmt_seconds(remaining)}.')
            return
        protection_remaining = get_assassination_protection(target_id)
        if protection_remaining > 0:
            await ctx.send(f'{member.mention} was recently hit and is under protection for another {fmt_seconds(protection_remaining)}.')
            return
        shield_remaining = get_protection_remaining(target_id)
        if shield_remaining > 0:
            await ctx.send(f'{member.mention} is shielded for another {fmt_seconds(shield_remaining)}')
            return
    attacker_cash = get_cash(attacker_id)
    attacker_charges = get_assassin_charges(attacker_id)
    if not privileged and attacker_charges <= 0:
        await ctx.send('you need a weapon to attempt an assassination. buy a knife (`!buy knife`, 1 use) or a gun (`!buy gun`, 2 uses) from `!shop`.')
        return
    if not privileged:
        assassin_charges[attacker_id] = attacker_charges - 1
        await save_inventory_data()
        last_assassinate[attacker_id] = int(time.time())
    success = random.random() < ASSASSINATE_SUCCESS_CHANCE
    if success:
        target_cash = get_cash(target_id)
        await set_cash_locked(target_id, 0, member)
        user_debt[target_id] = get_debt(target_id) + 10000
        last_assassinated_at[target_id] = int(time.time())
        await save_cash_data()
        await ctx.send(f"\U0001f480 Assassination succeeded! {member.mention} loses ${target_cash} and gains $10,000 debt. they're protected from further assassinations for {fmt_seconds(ASSASSINATE_TIMEOUT_SECONDS)}.")
    else:
        await set_cash_locked(attacker_id, 0, ctx.author)
        user_debt[attacker_id] = get_debt(attacker_id) + 10000
        await save_cash_data()
        await ctx.send(f'\u274c Assassination failed! {ctx.author.mention} loses all cash and gains $10,000 debt.')

@bot.command()
@admin_check()
async def reset(ctx, confirmation: str=''):
    if not is_active_channel(ctx.channel):
        return
    if confirmation.lower() != 'confirm':
        await ctx.send('\u26a0\ufe0f This wipes ALL bot data. Use `!reset confirm`.')
        return
    user_pools.clear()
    user_full_lines.clear()
    user_quotes.clear()
    recent_sentences.clear()
    user_cash.clear()
    user_debt.clear()
    tax_evasion_debt.clear()
    last_beg.clear()
    last_work.clear()
    last_pray.clear()
    last_loan.clear()
    last_debt_penalty.clear()
    last_tax.clear()
    last_assassinate.clear()
    last_assassinated_at.clear()
    last_nick_edit.clear()
    user_inventory.clear()
    protected_until.clear()
    lucky_charm_active.clear()
    assassin_charges.clear()
    brick_active.clear()
    luck_drug_until.clear()
    cash_locks.clear()
    for key in bot_stats.keys():
        bot_stats[key] = 0
    async with aiofiles.open(TEXT_FILE, 'w', encoding='utf-8') as f:
        await f.write('')
    await save_cash_data()
    await save_inventory_data()
    await ctx.send('\u26a0\ufe0f All memory and economy data wiped.')
    debug(f'Full reset performed by {ctx.author} ({ctx.author.id})')

@bot.command(name='shutdown')
@admin_check()
async def shutdown_command(ctx):
    if not is_active_channel(ctx.channel):
        return
    await ctx.send('\U0001f534 Saving data and shutting down Jachlam...')
    await graceful_shutdown()

@bot.command()
async def cash(ctx):
    if not is_active_channel(ctx.channel):
        return
    balance = get_cash(ctx.author.id)
    await update_cash_nick(ctx.author, get_display_cash(ctx.author.id))
    if ctx.author.id in brick_active:
        await ctx.send(f'{ctx.author.mention} actually has ${balance} (your Brick makes everyone else see ${get_display_cash(ctx.author.id)})')
    else:
        await ctx.send(f'{ctx.author.mention} has ${balance}')

@bot.command(aliases=['yn'])
async def yesorno(ctx, name: str, *, question: str=''):
    if not is_active_channel(ctx.channel):
        return
    answer = random.choice(['yes', 'no'])
    await ctx.send(f'{name.capitalize()}: {answer}')

@bot.command(name='image', aliases=['gif', 'img'])
async def random_image(ctx):
    if not is_active_channel(ctx.channel):
        return
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get('https://meme-api.com/gimme', timeout=10) as resp:
                if resp.status != 200:
                    await ctx.send("couldn't fetch an image right now, try again in a bit")
                    return
                data = await resp.json()
    except (aiohttp.ClientError, asyncio.TimeoutError):
        await ctx.send("couldn't fetch an image right now, try again in a bit")
        return
    url = data.get('url')
    if not url:
        await ctx.send("couldn't fetch an image right now, try again in a bit")
        return
    await ctx.send(url)

async def perform_nuke(channel):
    """Core nuke logic, reusable from both the !nuke command and the terminal."""
    recent_authors = await get_recent_human_members(channel, max_messages=200)
    deleted = 0
    try:
        deleted_msgs = await channel.purge(limit=200)
        deleted = len(deleted_msgs)
    except discord.HTTPException as exc:
        debug(f'Nuke purge failed: {exc}')
    timed_out = []
    for member in recent_authors:
        if is_money_admin(member.id):
            continue
        try:
            await member.timeout(timedelta(days=NUKE_TIMEOUT_DAYS), reason='Channel nuke')
            timed_out.append(member.display_name)
        except discord.HTTPException as exc:
            debug(f'Failed to timeout {member.display_name}: {exc}')
    summary = f'\U0001f4a5 nuked. {deleted} messages deleted.'
    if timed_out:
        summary += f" timed out for {NUKE_TIMEOUT_DAYS} days: {', '.join(timed_out)}."
    return summary

@bot.command()
@admin_check()
async def nuke(ctx, confirm: str=None):
    """Admin-only: purges the channel and times out everyone who posted in it."""
    if not is_active_channel(ctx.channel):
        return
    channel = ctx.channel
    if confirm != 'confirm':
        pending_nukes[channel.id] = ctx.author.id
        await ctx.send(f'\u26a0\ufe0f this will delete recent messages in this channel and timeout every non-admin who posted here for {NUKE_TIMEOUT_DAYS} days. run `!nuke confirm` within {NUKE_CONFIRM_WINDOW}s to go through with it.')

        async def expire_pending():
            await asyncio.sleep(NUKE_CONFIRM_WINDOW)
            pending_nukes.pop(channel.id, None)
        bot.loop.create_task(expire_pending())
        return
    if pending_nukes.get(channel.id) != ctx.author.id:
        await ctx.send('no pending nuke to confirm -- run `!nuke` first.')
        return
    pending_nukes.pop(channel.id, None)
    summary = await perform_nuke(channel)
    await channel.send(summary)
LEADERBOARD_SIZE = 10

@bot.command(aliases=['rich', 'top'])
async def leaderboard(ctx):
    if not is_active_channel(ctx.channel):
        return
    ranked = sorted(user_cash.items(), key=lambda pair: pair[1], reverse=True)
    ranked = [(uid, amount) for uid, amount in ranked if uid != bot_user_id]
    if not ranked:
        await ctx.send('nobody has any cash yet')
        return
    lines = []
    medals = {0: '\U0001f947', 1: '\U0001f948', 2: '\U0001f949'}
    for i, (uid, amount) in enumerate(ranked[:LEADERBOARD_SIZE]):
        guild_member = ctx.guild.get_member(uid) if ctx.guild is not None else None
        name = guild_member.display_name if guild_member is not None else f'user {uid}'
        name = _clean_display_name(name)
        rank_marker = medals.get(i, f'{i + 1}.')
        debt = get_debt(uid)
        debt_note = f' (debt ${debt})' if debt > 0 else ''
        lines.append(f'{rank_marker} **{name}** \u2014 ${get_display_cash(uid)}{debt_note}')
    embed = discord.Embed(title='cash leaderboard', description='\n'.join(lines), color=discord.Color.gold())
    await ctx.send(embed=embed)

def find_shop_item(query):
    """Match by item_id or by (case-insensitive) display name."""
    query = query.strip().lower().replace(' ', '_')
    if query in SHOP_ITEMS:
        return query
    for item_id, item in SHOP_ITEMS.items():
        if item['name'].lower().replace(' ', '_') == query:
            return item_id
    return None

@bot.command()
async def shop(ctx):
    if not is_active_channel(ctx.channel):
        return
    lines = [f"**{item['name']}** (`{item_id}`) \u2014 ${item['price']} \u2014 {item['description']}" for item_id, item in SHOP_ITEMS.items()]
    embed = discord.Embed(title='shop', description='\n'.join(lines) + '\n\nbuy with `!buy <item> [qty]`, use with `!use <item>`', color=discord.Color.blurple())
    await ctx.send(embed=embed)

@bot.command()
async def buy(ctx, item_name: str, qty: int=1):
    if not is_active_channel(ctx.channel):
        return
    if qty <= 0:
        await ctx.send('quantity must be more than 0')
        return
    item_id = find_shop_item(item_name)
    if item_id is None:
        await ctx.send(f"no item called '{item_name}'. check `!shop` for what's available.")
        return
    item = SHOP_ITEMS[item_id]
    cost = item['price'] * qty
    uid = ctx.author.id
    kind = item['kind']
    if kind in {'andy', 'brick'} and qty != 1:
        await ctx.send(f"you can only buy 1 {item['name']} at a time")
        return
    if kind == 'brick' and uid in brick_active:
        await ctx.send('you already have an active Brick')
        return
    async with get_cash_lock(uid):
        balance = get_cash(uid)
        if cost > balance:
            await ctx.send(f'that costs ${cost} and you only have ${balance}')
            return
        await set_cash(uid, balance - cost, ctx.author)
    if kind == 'assassin_weapon':
        charges = item['assassin_charges'] * qty
        assassin_charges[uid] = get_assassin_charges(uid) + charges
        await save_inventory_data()
        await ctx.send(f"bought {qty}x **{item['name']}** for ${cost}. assassination charges: {get_assassin_charges(uid)}. balance: ${get_cash(uid)}")
        return
    if kind == 'andy':
        if ANDY_USER_ID is not None:
            cut = max(1, int(get_cash(uid) * 0.1))
            await modify_cash(uid, -cut)
            await modify_cash(ANDY_USER_ID, cut)
        await ctx.send(f"bought {qty}x **{item['name']}** for ${cost}. balance: ${get_cash(uid)}")
        return
    if kind == 'brick':
        brick_active.add(uid)
        await save_inventory_data()
        await ctx.send(f"bought {qty}x **{item['name']}** for ${cost}. your displayed balance is now inflated {item['display_multiplier']}x -- everyone's going to think you're loaded.")
        return
    add_item(uid, item_id, qty)
    await save_inventory_data()
    await ctx.send(f"bought {qty}x **{item['name']}** for ${cost}. you now have {get_item_qty(uid, item_id)}x. balance: ${get_cash(uid)}")

@bot.command(aliases=['inv'])
async def inventory(ctx, member: discord.Member=None):
    if not is_active_channel(ctx.channel):
        return
    target = member or ctx.author
    inv = get_inventory(target.id)
    charges = get_assassin_charges(target.id)
    if not inv and charges <= 0:
        await ctx.send(f'{target.mention} has nothing in their inventory')
        return
    lines = [f"**{SHOP_ITEMS[item_id]['name']}** x{qty}" for item_id, qty in inv.items() if item_id in SHOP_ITEMS]
    if charges > 0:
        lines.append(f'\U0001f52a assassination charges: {charges}')
    protection_remaining = get_protection_remaining(target.id)
    if protection_remaining > 0:
        lines.append(f'\n\U0001f6e1\ufe0f protected for {fmt_seconds(protection_remaining)}')
    embed = discord.Embed(title=f"{target.display_name}'s inventory", description='\n'.join(lines), color=discord.Color.green())
    await ctx.send(embed=embed)

@bot.command()
async def use(ctx, item_name: str, target: str=None):
    if not is_active_channel(ctx.channel):
        return
    member = None
    amount = 1
    if target is not None:
        try:
            amount = int(target)
        except ValueError:
            try:
                member = await commands.MemberConverter().convert(ctx, target)
            except commands.BadArgument:
                await ctx.send('invalid member or amount')
                return
    item_id = find_shop_item(item_name)
    if item_id is None:
        await ctx.send(f"no item called '{item_name}'")
        return
    uid = ctx.author.id
    if get_item_qty(uid, item_id) <= 0:
        await ctx.send(f"you don't have a {SHOP_ITEMS[item_id]['name']}. buy one with `!buy {item_id}`")
        return
    item = SHOP_ITEMS[item_id]
    kind = item['kind']
    if kind == 'shield':
        remove_item(uid, item_id)
        hours = item['shield_hours']
        protected_until[uid] = int(time.time()) + hours * 3600
        await save_inventory_data()
        await ctx.send(f'\U0001f6e1\ufe0f {ctx.author.mention} is now protected from steal/assassinate for {hours} hours')
        return
    if kind == 'lucky_charm':
        remove_item(uid, item_id)
        lucky_charm_active.add(uid)
        await save_inventory_data()
        boost_pct = int(item.get('boost', 0) * 100)
        await ctx.send(f"\U0001f340 {ctx.author.mention}'s next `!gamble` win chance is boosted by {boost_pct}% (not guaranteed)")
        return
    if kind == 'debt_relief':
        current_debt = get_debt(uid)
        if current_debt <= 0:
            await ctx.send("you don't have any debt to clear")
            return
        remove_item(uid, item_id)
        user_debt[uid] = max(0, current_debt - item['debt_amount'])
        await save_cash_data()
        await save_inventory_data()
        await ctx.send(f"cleared ${item['debt_amount']} of debt. remaining debt: ${get_debt(uid)}")
        return
    if kind == 'mystery_box':
        remove_item(uid, item_id)
        payout = random.randint(item['box_min'], item['box_max'])
        await modify_cash(uid, payout, ctx.author)
        await save_inventory_data()
        await ctx.send(f'\U0001f4e6 the box had ${payout} inside. new balance: ${get_cash(uid)}')
        return
    if kind == 'mystery_pack':
        remove_item(uid, item_id)
        await save_inventory_data()
        roll = random.random()
        if roll < 0.35:
            payout = random.randint(200, 4000)
            await modify_cash(uid, payout, ctx.author)
            await ctx.send(f'the pack had ${payout} cash in it! new balance: ${get_cash(uid)}')
        elif roll < 0.6:
            lost = min(get_cash(uid), random.randint(200, 2000))
            await modify_cash(uid, -lost, ctx.author)
            await ctx.send(f'something inside bit you. you lost ${lost}. new balance: ${get_cash(uid)}')
        elif roll < 0.85:
            debt_added = random.randint(500, 3000)
            user_debt[uid] = get_debt(uid) + debt_added
            last_debt_penalty[uid] = int(time.time())
            await save_cash_data()
            await ctx.send(f'whatever was in there put you ${debt_added} in debt. total debt: ${get_debt(uid)}')
        else:
            await set_cash_locked(uid, 0, ctx.author)
            await ctx.send(f'you did NOT want to know what was in there. {ctx.author.mention} loses all their cash. balance: ${get_cash(uid)}')
        return
    if kind == 'novelty':
        remove_item(uid, item_id)
        await save_inventory_data()
        if member is not None:
            await ctx.send(f"\U0001f4a9 {ctx.author.mention} hurls a {item['name'].lower()} at {member.mention}. direct hit.")
        else:
            await ctx.send(f"\U0001f4a9 {ctx.author.mention} just... has a {item['name'].lower()} now. what are you going to do with it")
        return
    if kind == 'double_money':
        remove_item(uid, item_id)
        async with get_cash_lock(uid):
            balance = get_cash(uid)
            new_balance = balance * 2
            await set_cash(uid, new_balance, ctx.author)
        await save_inventory_data()
        await ctx.send(f'\u2728 Jachlam doubled your money! ${balance} -> ${new_balance}')
        return
    if kind == 'punish_orion':
        if amount < 1:
            await ctx.send('amount must be at least 1')
            return
        if not remove_item(uid, item_id, amount):
            await ctx.send(f"you only have {get_item_qty(uid, item_id)} Jachlam's Punishment(s)")
            return
        await save_inventory_data()
        if ORION_USER_ID is None:
            await ctx.send('Jachlam has no one to punish right now.')
            return
        user_debt[ORION_USER_ID] = get_debt(ORION_USER_ID) + item['debt_amount'] * amount
    last_debt_penalty[ORION_USER_ID] = int(time.time())
    await save_cash_data()
    await ctx.send(f"\u26a1 Jachlam smites Orion with ${item['debt_amount'] * amount} debt. their total debt: ${get_debt(ORION_USER_ID)}")
    return
    if kind == 'luck_drug':
        remove_item(uid, item_id)
        hours = item['luck_hours']
        luck_drug_until[uid] = int(time.time()) + hours * 3600
        await save_inventory_data()
        flavor = random.choice(MYSTERY_DRUG_FLAVORS)
        await ctx.send(f'{ctx.author.mention} takes {flavor}. your `!gamble` luck is boosted for {hours} hour(s).')
        return
    await ctx.send("that item doesn't do anything yet")

@bot.command()
@admin_check()
async def giveitem(ctx, member: discord.Member, item_name: str, qty: int=1):
    if not is_active_channel(ctx.channel):
        return
    if qty <= 0:
        await ctx.send('quantity must be more than 0')
        return
    item_id = find_shop_item(item_name)
    if item_id is None:
        await ctx.send(f"no item called '{item_name}'")
        return
    add_item(member.id, item_id, qty)
    await save_inventory_data()
    await ctx.send(f"gave {qty}x **{SHOP_ITEMS[item_id]['name']}** to {member.mention}")

@bot.command()
async def stats(ctx, member: discord.Member=None):
    if not is_active_channel(ctx.channel):
        return
    target = member if member is not None else ctx.author
    uid = target.id
    cash = get_cash(uid)
    debt = get_debt(uid)
    beg_cd = get_remaining_cooldown(last_beg.get(uid, 0), BEG_COOLDOWN)
    work_cd = get_remaining_cooldown(last_work.get(uid, 0), WORK_COOLDOWN)
    pray_cd = get_remaining_cooldown(last_pray.get(uid, 0), PRAY_COOLDOWN)
    loan_cd = get_remaining_cooldown(last_loan.get(uid, 0), LOAN_COOLDOWN)
    tax_cd = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)
    if debt > 0:
        debt_penalty_cd = get_remaining_cooldown(last_debt_penalty.get(uid, int(time.time())), DEBT_PENALTY_INTERVAL_SECONDS)
        debt_penalty_text = fmt_seconds(debt_penalty_cd)
    else:
        debt_penalty_text = 'none'
    embed = discord.Embed(title=f'stats: {target.display_name}', color=discord.Color.green())
    embed.add_field(name='cash', value=f'${cash}', inline=True)
    embed.add_field(name='debt', value=f'${debt}', inline=True)
    embed.add_field(name='loan status', value='active' if debt > 0 else 'clear', inline=True)
    embed.add_field(name='beg cooldown', value=fmt_seconds(beg_cd), inline=True)
    embed.add_field(name='work cooldown', value=fmt_seconds(work_cd), inline=True)
    embed.add_field(name='pray cooldown', value=fmt_seconds(pray_cd), inline=True)
    embed.add_field(name='loan cooldown', value=fmt_seconds(loan_cd), inline=True)
    embed.add_field(name='tax due in', value=fmt_seconds(tax_cd), inline=True)
    embed.add_field(name='debt penalty in', value=debt_penalty_text, inline=True)
    await ctx.send(embed=embed)

@bot.command()
@admin_check()
async def setcash(ctx, member: discord.Member, amount: int):
    if not is_active_channel(ctx.channel):
        return
    await set_cash_locked(member.id, amount, member, force_nick=True)
    await ctx.send(f'set {member.mention} cash to ${get_cash(member.id)}')

@bot.command()
@admin_check()
async def resetuser(ctx, member: discord.Member):
    if not is_active_channel(ctx.channel):
        return
    clear_user_state(member.id)
    await update_cash_nick(member, STARTING_CASH, force=True)
    await save_cash_data()
    await ctx.send(f'reset {member.mention}: cash ${STARTING_CASH}, debt $0, and all cooldowns cleared')

@bot.command()
@admin_check()
async def setdebt(ctx, member: discord.Member, amount: int):
    if not is_active_channel(ctx.channel):
        return
    user_debt[member.id] = max(0, int(amount))
    if user_debt[member.id] == 0:
        last_debt_penalty.pop(member.id, None)
    else:
        last_debt_penalty[member.id] = int(time.time())
    await save_cash_data()
    await ctx.send(f'set {member.mention} debt to ${get_debt(member.id)}')

@bot.command()
@admin_check()
async def adddebt(ctx, first: str, second: str):
    if not is_active_channel(ctx.channel):
        return
    member, amount = await resolve_member_and_amount(ctx, first, second)
    if member is None or amount is None:
        await ctx.send('usage: !adddebt @member 1000 or !adddebt 1000 @member')
        return
    if amount <= 0:
        await ctx.send('amount must be more than 0')
        return
    user_debt[member.id] = get_debt(member.id) + amount
    last_debt_penalty[member.id] = int(time.time())
    await save_cash_data()
    await ctx.send(f'added ${amount} debt to {member.mention}. new debt: ${get_debt(member.id)}')

@bot.command()
@admin_check()
async def takedebt(ctx, first: str, second: str):
    if not is_active_channel(ctx.channel):
        return
    member, amount = await resolve_member_and_amount(ctx, first, second)
    if member is None or amount is None:
        await ctx.send('usage: !takedebt @member 1000 or !takedebt 1000 @member')
        return
    if amount <= 0:
        await ctx.send('amount must be more than 0')
        return
    user_debt[member.id] = max(0, get_debt(member.id) - amount)
    if user_debt[member.id] == 0:
        last_debt_penalty.pop(member.id, None)
    await save_cash_data()
    await ctx.send(f'took ${amount} debt from {member.mention}. new debt: ${get_debt(member.id)}')

@bot.command()
@admin_check()
async def setbotcash(ctx, amount: int):
    if not is_active_channel(ctx.channel):
        return
    if bot_user_id is None:
        await ctx.send('bot cash is not ready yet')
        return
    await set_cash_locked(bot_user_id, amount, ctx.guild.get_member(bot_user_id) if ctx.guild is not None else None, force_nick=True)
    await ctx.send(f'set bot cash to ${get_bot_cash()}')

@bot.command()
@admin_check()
async def addcash(ctx, member: discord.Member, amount: int):
    if not is_active_channel(ctx.channel):
        return
    if amount <= 0:
        await ctx.send('amount must be more than 0')
        return
    await modify_cash(member.id, amount, member, force_nick=True)
    await ctx.send(f'added ${amount} to {member.mention}. new cash: ${get_cash(member.id)}')

@bot.command()
@admin_check()
async def takecash(ctx, member: discord.Member, amount: int):
    if not is_active_channel(ctx.channel):
        return
    if amount <= 0:
        await ctx.send('amount must be more than 0')
        return
    await modify_cash(member.id, -amount, member, force_nick=True)
    await ctx.send(f'took ${amount} from {member.mention}. new cash: ${get_cash(member.id)}')

@bot.command()
async def gamble(ctx, amount: str):
    if not is_active_channel(ctx.channel):
        return
    balance = get_cash(ctx.author.id)
    if amount.lower() == 'all':
        bet = balance
    else:
        try:
            bet = int(amount)
        except ValueError:
            await ctx.send("use a number or 'all' (example: !gamble 200)")
            return
    if bet <= 0:
        await ctx.send('bet must be more than 0')
        return
    if bet > balance:
        await ctx.send("you don't have that much cash")
        return
    win_chance = GAMBLE_WIN_CHANCE
    if has_luck_boost(ctx.author.id):
        win_chance = min(0.95, win_chance + SHOP_ITEMS['mystery_drug']['luck_boost'])
    used_charm = ctx.author.id in lucky_charm_active
    if used_charm:
        win_chance = min(0.95, win_chance + SHOP_ITEMS['lucky_charm']['boost'])
    won = random.random() < win_chance
    if used_charm:
        lucky_charm_active.discard(ctx.author.id)
        await save_inventory_data()
    await modify_cash(ctx.author.id, bet if won else -bet, ctx.author)
    new_balance = get_cash(ctx.author.id)
    if won:
        bot_stats['gamble_wins'] += 1
        await save_cash_data()
        await ctx.send(f'you won ${bet}. new balance: ${new_balance}')
    else:
        bot_stats['gamble_losses'] += 1
        await save_cash_data()
        await ctx.send(f'you lost ${bet}. new balance: ${new_balance}')

@bot.command()
async def beg(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    current_cash = get_cash(uid)
    remaining = get_remaining_cooldown(last_beg.get(uid, 0), BEG_COOLDOWN)
    if remaining > 0:
        await ctx.send(f'you can beg again in {fmt_seconds(remaining)}')
        return
    reward = random.randint(BEG_MIN, BEG_MAX)
    last_beg[uid] = int(time.time())
    await modify_cash(uid, reward, ctx.author)
    await ctx.send(f'someone gave you ${reward}. new balance: ${get_cash(uid)}')

@bot.command()
async def work(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    current_cash = get_cash(uid)
    remaining = get_remaining_cooldown(last_work.get(uid, 0), WORK_COOLDOWN)
    if remaining > 0:
        await ctx.send(f'you can work again in {fmt_seconds(remaining)}')
        return
    reward = random.randint(WORK_MIN, WORK_MAX)
    last_work[uid] = int(time.time())
    await modify_cash(uid, reward, ctx.author)
    await ctx.send(f'you worked a shift and earned ${reward}. new balance: ${get_cash(uid)}')

@bot.command()
async def pray(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    if has_tax_evasion_debt(uid):
        await ctx.send('you cannot pray while tax evasion debt is outstanding')
        return
    remaining = get_remaining_cooldown(last_pray.get(uid, 0), PRAY_COOLDOWN)
    if remaining > 0:
        await ctx.send(f'you can pray to jachlam again in {fmt_seconds(remaining)}')
        return
    last_pray[uid] = int(time.time())
    if random.random() < PRAY_SUCCESS_CHANCE:
        reward = random.randint(PRAY_MIN, PRAY_MAX)
        await modify_cash(uid, reward, ctx.author)
        await ctx.send(f'you prayed to jachlam and were blessed with ${reward}. new balance: ${get_cash(uid)}')
        return
    await save_cash_data()
    await ctx.send('you prayed to jachlam, but received no blessing this time')

@bot.command()
async def debt(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    debt_amount = get_debt(uid)
    if debt_amount <= 0:
        await ctx.send(f'{ctx.author.mention} debt: $0 | cash: ${get_cash(uid)}')
        return
    remaining = get_remaining_cooldown(last_debt_penalty.get(uid, int(time.time())), DEBT_PENALTY_INTERVAL_SECONDS)
    await ctx.send(f'{ctx.author.mention} debt: ${debt_amount} | cash: ${get_cash(uid)} | next overdue penalty in {fmt_seconds(remaining)}')

@bot.command()
async def loan(ctx, amount: str):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    existing_debt = get_debt(uid)
    if existing_debt > 0:
        await ctx.send(f'pay your current debt first with !repay. debt: ${existing_debt}')
        return
    remaining = get_remaining_cooldown(last_loan.get(uid, 0), LOAN_COOLDOWN)
    if remaining > 0:
        await ctx.send(f'you can take another loan in {fmt_seconds(remaining)}')
        return
    try:
        principal = int(amount)
    except ValueError:
        await ctx.send(f'use a number between {LOAN_MIN} and {LOAN_MAX} (example: !loan 500)')
        return
    if principal < LOAN_MIN or principal > LOAN_MAX:
        await ctx.send(f'loan must be between ${LOAN_MIN} and ${LOAN_MAX}')
        return
    debt_total = principal + max(1, int(principal * LOAN_INTEREST_RATE))
    last_loan[uid] = int(time.time())
    last_debt_penalty[uid] = int(time.time())
    user_debt[uid] = debt_total
    await modify_cash(uid, principal, ctx.author)
    await save_cash_data()
    await ctx.send(f'loan approved: +${principal} cash. total debt is ${debt_total} (includes {int(LOAN_INTEREST_RATE * 100)}% interest)')

@bot.command()
async def repay(ctx, amount: str):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    current_debt = get_debt(uid)
    if current_debt <= 0:
        await ctx.send('you have no debt')
        return
    balance = get_cash(uid)
    if balance <= 0:
        await ctx.send('you have no cash to repay with')
        return
    if amount.lower() == 'all':
        payment = min(balance, current_debt)
    else:
        try:
            payment = int(amount)
        except ValueError:
            await ctx.send("use a number or 'all' (example: !repay 300)")
            return
    if payment <= 0:
        await ctx.send('repay amount must be more than 0')
        return
    payment = min(payment, balance, current_debt)
    user_debt[uid] = current_debt - payment
    if user_debt[uid] <= 0:
        user_debt[uid] = 0
        last_debt_penalty.pop(uid, None)
        clear_tax_evasion_flag(uid)
    await modify_cash(uid, -payment, ctx.author)
    await save_cash_data()
    if user_debt[uid] == 0:
        await ctx.send(f'debt fully repaid. remaining cash: ${get_cash(uid)}')
    else:
        await ctx.send(f'paid ${payment}. remaining debt: ${user_debt[uid]} | cash: ${get_cash(uid)}')

@bot.command()
async def give(ctx, member: discord.Member, amount: str):
    if not is_active_channel(ctx.channel):
        return
    giver_id = ctx.author.id
    receiver_id = member.id
    if giver_id == receiver_id:
        await ctx.send("you can't give money to yourself")
        return
    giver_balance = get_cash(giver_id)
    if amount.lower() == 'all':
        transfer = giver_balance
    else:
        try:
            transfer = int(amount)
        except ValueError:
            await ctx.send("use a number or 'all' (example: !give @user 200)")
            return
    if transfer <= 0:
        await ctx.send('amount must be more than 0')
        return
    if transfer > giver_balance:
        await ctx.send("you don't have that much cash")
        return
    await modify_cash(giver_id, -transfer, ctx.author)
    await modify_cash(receiver_id, transfer, member)
    bot_stats['given'] += transfer
    if bot_user_id is not None and receiver_id == bot_user_id:
        bot_stats['received'] += transfer
    await save_cash_data()
    await ctx.send(f'{ctx.author.mention} gave ${transfer} to {member.mention}. balances: you ${get_cash(giver_id)}, them ${get_cash(receiver_id)}')

@bot.command()
async def steal(ctx, member: discord.Member, amount: str):
    if not is_active_channel(ctx.channel):
        return
    thief_id = ctx.author.id
    target_id = member.id
    if thief_id == target_id:
        await ctx.send("you can't steal from yourself")
        return
    shield_remaining = get_protection_remaining(target_id)
    if shield_remaining > 0:
        await ctx.send(f'{member.mention} is shielded for another {fmt_seconds(shield_remaining)}')
        return
    thief_balance = get_cash(thief_id)
    target_balance = get_cash(target_id)
    if target_balance <= 0:
        await ctx.send('that user has no money to steal')
        return
    if amount.lower() == 'all':
        requested = target_balance
    else:
        try:
            requested = int(amount)
        except ValueError:
            await ctx.send("use a number or 'all' (example: !steal @user 150)")
            return
    if requested <= 0:
        await ctx.send('amount must be more than 0')
        return
    steal_amount = min(requested, target_balance)
    success = random.random() < STEAL_SUCCESS_CHANCE
    if success:
        bot_stats['steal_success'] += 1
        await modify_cash(thief_id, steal_amount, ctx.author)
        await modify_cash(target_id, -steal_amount, member)
        await save_cash_data()
        await ctx.send(f'steal success: {ctx.author.mention} stole ${steal_amount} from {member.mention}. balances: you ${get_cash(thief_id)}, them ${get_cash(target_id)}')
        return
    penalty = max(1, int(steal_amount * STEAL_FAIL_PENALTY_RATE))
    penalty = min(penalty, thief_balance)
    if penalty > 0:
        bot_stats['steal_fail'] += 1
        await modify_cash(thief_id, -penalty, ctx.author)
        await modify_cash(target_id, penalty, member)
        await save_cash_data()
        await ctx.send(f'steal failed: you paid ${penalty} to {member.mention}. balances: you ${get_cash(thief_id)}, them ${get_cash(target_id)}')
    else:
        bot_stats['steal_fail'] += 1
        await save_cash_data()
        await ctx.send('steal failed, but you had no money for a penalty')

@bot.command()
async def botstats(ctx):
    if not is_active_channel(ctx.channel):
        return
    await ctx.send('\n'.join([f'bot cash: ${get_bot_cash()}', f"messages seen: {bot_stats['messages_seen']}", f"replies sent: {bot_stats['replies_sent']}", f"tax collected: ${bot_stats['tax_collected']}", f"gamble W/L: {bot_stats['gamble_wins']}/{bot_stats['gamble_losses']}", f"steal S/F: {bot_stats['steal_success']}/{bot_stats['steal_fail']}", f"given/received: ${bot_stats['given']}/${bot_stats['received']}"]))

@bot.command()
async def taxinfo(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    balance = get_cash(uid)
    rate = tax_rate_for_balance(balance)
    remaining = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)
    if remaining > 0:
        await ctx.send(f'{ctx.author.mention} tax bracket: {int(rate * 100)}% on ${balance}. next tax in {fmt_seconds(remaining)}')
    else:
        await ctx.send(f'{ctx.author.mention} tax bracket: {int(rate * 100)}% on ${balance}. tax is due now')

@bot.command(name='evade')
async def evade_tax(ctx):
    if not is_active_channel(ctx.channel):
        return
    uid = ctx.author.id
    tax_amount, rate, remaining = get_tax_due(uid, ignore_timer=True)
    await ctx.send(f'DEBUG: balance=${get_cash(uid):,}, tax=${tax_amount:,}, rate={rate}, remaining={remaining}')
    if tax_amount <= 0:
        await ctx.send('you do not owe any tax right now')
        return
    tax_evasion_count[uid] = tax_evasion_count.get(uid, 0) + 1
    last_tax[uid] = int(time.time())
    await save_cash_data()
    await ctx.send(f'\U0001f9fe {ctx.author.mention} evaded **${tax_amount}** in tax. the Department of Jachlam Affairs has been notified.')

@bot.command()
async def quote(ctx, member: discord.Member=None):
    if not is_active_channel(ctx.channel):
        return
    if member is not None:
        pool = user_quotes.get(member.id, [])
        if not pool:
            await ctx.send(f'no quotes saved for {member.mention}')
            return
        await ctx.send(f'{member.mention}: "{random.choice(pool)}"')
        return
    all_quotes = []
    for quotes in user_quotes.values():
        all_quotes.extend(quotes)
    if not all_quotes:
        await ctx.send('no quotes saved yet')
        return
    await ctx.send(f'"{random.choice(all_quotes)}"')

@bot.command()
async def quoteadd(ctx, *, text: str):
    if not is_active_channel(ctx.channel):
        return
    phrase = text.strip()
    if not phrase:
        await ctx.send('usage: !quoteadd <text>')
        return
    uid = ctx.author.id
    user_quotes.setdefault(uid, []).append(phrase)
    await append_corpus_line(uid, phrase, is_quote=True)
    await ctx.send('quote saved')

@bot.command()
async def quotereply(ctx):
    if not is_active_channel(ctx.channel):
        return
    ref = ctx.message.reference
    if ref is None or ref.message_id is None:
        await ctx.send('reply to a message, then use !quotereply')
        return
    try:
        if isinstance(ref.resolved, discord.Message):
            target_message = ref.resolved
        else:
            target_message = await ctx.channel.fetch_message(ref.message_id)
    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
        await ctx.send('could not find that replied message')
        return
    phrase = target_message.content.strip()
    if not phrase:
        await ctx.send('that message has no text to quote')
        return
    uid = target_message.author.id
    user_quotes.setdefault(uid, []).append(phrase)
    await append_corpus_line(uid, phrase, is_quote=True)
    await ctx.send(f'quote saved for {target_message.author.mention}')

@bot.command()
async def quotes(ctx, member: discord.Member=None, page: int=1):
    if not is_active_channel(ctx.channel):
        return
    page = max(1, page)
    if member is not None:
        entries = [(member.id, quote_text) for quote_text in user_quotes.get(member.id, [])]
        title = f'quotes for {member.display_name}'
    else:
        entries = []
        for uid, quote_list in user_quotes.items():
            for quote_text in quote_list:
                entries.append((uid, quote_text))
        title = 'all quotes'
    if not entries:
        await ctx.send('no quotes saved yet')
        return
    total_pages = max(1, (len(entries) + QUOTES_PAGE_SIZE - 1) // QUOTES_PAGE_SIZE)
    if page > total_pages:
        await ctx.send(f'page out of range. max page is {total_pages}')
        return
    start = (page - 1) * QUOTES_PAGE_SIZE
    end = min(start + QUOTES_PAGE_SIZE, len(entries))
    lines = []
    for i, (uid, quote_text) in enumerate(entries[start:end], start=start + 1):
        safe_text = quote_text.replace('\n', ' ').strip()
        if len(safe_text) > 180:
            safe_text = safe_text[:177] + '...'
        if member is None:
            guild_member = ctx.guild.get_member(uid) if ctx.guild is not None else None
            author_name = guild_member.display_name if guild_member is not None else f'user {uid}'
            lines.append(f'{i}. **{author_name}**: "{safe_text}"')
        else:
            lines.append(f'{i}. "{safe_text}"')
    embed = discord.Embed(title=title, description='\n'.join(lines), color=discord.Color.blue())
    embed.set_footer(text=f'page {page}/{total_pages} \u2022 total quotes: {len(entries)}')
    await ctx.send(embed=embed)

@bot.command()
@admin_check()
async def ping(ctx, member: discord.Member=None):
    if not is_active_channel(ctx.channel):
        return
    target = member or ctx.author
    for i in range(20):
        await ctx.send(f'{target.mention}')
        await asyncio.sleep(0.8)

@bot.command()
@admin_check()
async def forcetaxall(ctx):
    if not is_active_channel(ctx.channel):
        return
    total_collected = 0
    users_taxed = 0
    for uid in list(user_cash.keys()):
        last_tax[uid] = 0
        tax_amount, rate = await apply_tax_if_due(uid, ctx.guild.get_member(uid))
        users_taxed += 1
        if tax_amount > 0:
            total_collected += tax_amount
    await ctx.send(f'forced tax on {users_taxed} users, collected ${total_collected}')

@bot.command()
@admin_check()
async def setup(ctx, action: str=None, channel_id: str=None):
    """
    !setup                    -- show current mode
    !setup all                -- run in every text channel of the server (default)
    !setup <channel_id>       -- restrict to just that one channel
    !setup exclude <chan_id>  -- sit out one channel while otherwise server-wide
    !setup include <chan_id>  -- undo an exclude
    """
    global CHANNEL_ID, SERVER_WIDE_MODE
    if action is None:
        if SERVER_WIDE_MODE:
            excluded = ', '.join((str(c) for c in EXCLUDED_CHANNEL_IDS)) or 'none'
            await ctx.send(f'mode: server-wide (all channels). excluded: {excluded}')
        else:
            await ctx.send(f'mode: single channel ({CHANNEL_ID})')
        return
    action_lower = action.lower()
    if action_lower == 'all':
        SERVER_WIDE_MODE = True
        await save_cash_data()
        await ctx.send('now active in every text channel of the server')
        return
    if action_lower in {'exclude', 'include'}:
        if channel_id is None:
            await ctx.send(f'usage: !setup {action_lower} <channel_id>')
            return
        try:
            cid = int(channel_id)
        except ValueError:
            await ctx.send('channel id must be a number')
            return
        if action_lower == 'exclude':
            EXCLUDED_CHANNEL_IDS.add(cid)
            await ctx.send(f'now sitting out of channel {cid}')
        else:
            EXCLUDED_CHANNEL_IDS.discard(cid)
            await ctx.send(f'no longer excluding channel {cid}')
        await save_cash_data()
        return
    try:
        CHANNEL_ID = int(action)
        SERVER_WIDE_MODE = False
        await save_cash_data()
        await ctx.send(f'restricted to single channel {CHANNEL_ID}')
    except ValueError:
        await ctx.send('usage: !setup | !setup all | !setup <channel_id> | !setup exclude/include <channel_id>')

@bot.command(name='sleep')
@admin_check()
async def sleep_cmd(ctx):
    if not is_active_channel(ctx.channel):
        return
    global sleep_override, bot_is_asleep
    sleep_override = True
    if not bot_is_asleep:
        bot_is_asleep = True
        if is_bedtime():
            await ctx.send('going to bed, back at 7am')
        else:
            await ctx.send(random.choice(['aww, do i have to? fine... going to bed early i guess :(', "but it's not even bedtime yet... okay, going to sleep i guess.", "no fair, i'm not even tired. night i guess."]))
    else:
        await ctx.send('already asleep')

@bot.command(name='wake')
@admin_check()
async def wake_cmd(ctx):
    if not is_active_channel(ctx.channel):
        return
    global sleep_override, bot_is_asleep
    sleep_override = None
    bot_is_asleep = False
    await ctx.send("morning, i'm awake")

@bot.command(name='global')
async def global_mode(ctx):
    global mode, track_target
    mode = 'global'
    track_target = None
    await ctx.send('back to global mode')
    debug('Switched to GLOBAL')

@bot.command()
@admin_check()
async def imitate(ctx, member: discord.Member):
    global mode, track_target
    mode = 'track'
    track_target = member.id
    await ctx.send(f'imitating {member.display_name}')
    debug(f'Switched to TRACK ({member.id})')
    await asyncio.sleep(TRACK_DURATION)
    mode = 'global'
    track_target = None
    await ctx.send('imitation ended')
    debug('Track expired')
CHANGELOG_PAGES = [{'date': 'August 22, 2026', 'title': 'Economy and Stability Update', 'changes': ['Added enforceable financial audits with tax-evasion fines.', 'Added persistent quote commands.', 'Added clean Discord shutdown using `!shutdown`.', 'Protected the global reset with admin permission and confirmation.', 'Prevented duplicate background tasks after reconnecting.', 'Added atomic cash and inventory saving.', 'Fixed the internal channel-nuke helper.', 'Made every emoji and special character source-encoding safe.', 'Blocked empty or damaged resync files from erasing live balances.', 'Added automatic `.bak` backups before economy save files are replaced.', 'Added the `!changelog`, `!updates`, and `!patchnotes` commands.', 'Added a versioned system boot sequence with subsystem status checks.', 'Reformatted the complete bot to reduce source size without removing functionality.'], 'url': None}, {'date': 'August 21, 2026', 'title': 'Response and Member Update', 'changes': ['Enhanced fallback messages and bot responses.', 'Added Discord member intents.', 'Prevented the bot from triggering itself.'], 'url': 'https://github.com/veroteknic/jachlam/commit/c906aa7137f28a4644b06f1f82e9db181363c2bb'}, {'date': 'August 20, 2026', 'title': 'GIF, Nuke and Admin Update', 'changes': ['Added repeated-GIF timeouts.', 'Added the channel nuke command.', 'Improved nickname updates and admin checks.'], 'url': 'https://github.com/veroteknic/jachlam/commits?since=2026-08-20&until=2026-08-21'}, {'date': 'June 21, 2026', 'title': 'The Random Stuff Update', 'changes': ['Updated the main bot code.', 'Added random stuff. Nobody remembers what it was.'], 'url': 'https://github.com/veroteknic/jachlam/commits?since=2026-06-21&until=2026-06-22'}, {'date': 'April 14, 2026', 'title': 'Tax Update', 'changes': ['Disabled the automatic bot economy.', 'Changed the tax calculation system.'], 'url': 'https://github.com/veroteknic/jachlam/commit/a6acbcbf8531ca9c4ba2f9f10fc83419ee62a084'}, {'date': 'April 4, 2026', 'title': 'Assassination Update', 'changes': ['Added assassination cooldowns and penalties.', 'Improved assassination logic, feedback, and admin checks.', 'Improved bot nickname handling.'], 'url': 'https://github.com/veroteknic/jachlam/commits?since=2026-04-04&until=2026-04-05'}]

@bot.command(name='changelog', aliases=['updates', 'patchnotes'])
async def changelog(ctx, page: int=1):
    if not is_active_channel(ctx.channel):
        return
    total_pages = len(CHANGELOG_PAGES)
    if not 1 <= page <= total_pages:
        await ctx.send(f'choose a changelog page from `1` to `{total_pages}`.')
        return
    entry = CHANGELOG_PAGES[page - 1]
    embed = discord.Embed(title=f"\U0001f4dc Jachlam Changelog - {entry['date']}", description=f"## {entry['title']}", color=discord.Color.gold())
    embed.add_field(name='Changes', value='\n'.join((f'\u2022 {change}' for change in entry['changes'])), inline=False)
    if entry['url']:
        embed.add_field(name='GitHub', value=f"[View changes on GitHub]({entry['url']})", inline=False)
    embed.set_footer(text=f'Page {page}/{total_pages} | Use !changelog <page> for older updates')
    await ctx.send(embed=embed)
if __name__ == '__main__':
    if not TOKEN:
        raise ValueError('No token found. Make sure DISCORD_TOKEN or TOKEN is set in your environment variables.')
    bot.run(TOKEN)
