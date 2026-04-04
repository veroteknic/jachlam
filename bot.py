import asyncio
import discord
from discord.ext import commands
import aiofiles
import random
import os
import json
import re
import time
from dotenv import load_dotenv
from datetime import timedelta
# Load environment variables
load_dotenv()

TOKEN = os.getenv("DISCORD_TOKEN") or os.getenv("TOKEN")
# ================= CONFIG =================

CHANNEL_ID_DEFAULT = 1409844931761279019
MONEY_ADMIN_USER_ID = 1055064009457537024
TEXT_FILE = "markov_corpus.txt"
CASH_FILE = "cash_data.json"
CORPUS_QUOTE_PREFIX = "Q:"

DEBUG = True

MAX_PHRASES = 400
MAX_RECENT_PHRASES = 80
MAX_RECENT_SENTENCES = 15
MAX_REPLY_PHRASES = 3
SILENCE_CHANCE = 0.3
MAX_TRACK_LINES = 30000
QUOTES_PAGE_SIZE = 5

TRACK_DURATION = 300  # seconds

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
LOAN_INTEREST_RATE = 0.20
DEBT_PENALTY_INTERVAL_SECONDS = 6 * 60 * 60
DEBT_PENALTY_CASH_FEE = 15
DEBT_PENALTY_DEBT_RATE = 0.03
TAX_INTERVAL_SECONDS = 60 * 60  # 1 hour
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
ASSASSINATE_TIMEOUT_SECONDS = 2 * 60 * 60  # 2 hours
ASSASSINATE_COOLDOWN = 600  # optional: 10 minutes
last_assassinate = {}

# Progressive tax rate based on current balance.
TAX_BRACKETS = [
  (20000, 0.10),
  (10000, 0.07),
  (5000, 0.04),
  (1000, 0.02),
  (0, 0.00),
]

FALLBACKS = ["dang same", "yo fr", "ehh idk", "😭"]

# ================= DEBUG =================


def debug(msg):
  if DEBUG:
    print(f"[DEBUG] {msg}")


# ================= DISCORD =================

intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents)

# ================= STATE =================

user_pools = {}  # {user_id: [phrases]}
user_full_lines = {}  # {user_id: [full raw messages]}
user_quotes = {}  # {user_id: [quote lines]}
recent_sentences = []
user_cash = {}  # {user_id: cash}
user_debt = {}  # {user_id: debt}
last_beg = {}  # {user_id: unix_ts}
last_work = {}  # {user_id: unix_ts}
last_pray = {}  # {user_id: unix_ts}
last_loan = {}  # {user_id: unix_ts}
last_debt_penalty = {}  # {user_id: unix_ts}
last_tax = {}  # {user_id: unix_ts}
bot_user_id = None
CHANNEL_ID = CHANNEL_ID_DEFAULT
bot_stats = {
  "messages_seen": 0,
  "replies_sent": 0,
  "tax_collected": 0,
  "gamble_wins": 0,
  "gamble_losses": 0,
  "steal_success": 0,
  "steal_fail": 0,
  "given": 0,
  "received": 0,
}

reaction_starts = []
reaction_middles = []
reaction_ends = []
MAX_REACTIONS = 200

message_counter = 0
messages_per_reply = random.randint(1, 5)

mode = "global"  # "global" or "track"
track_target = None

# ================= HELPERS =================

def can_use_assassinate(uid):
  remaining = get_remaining_cooldown(last_assassinate.get(uid, 0), ASSASSINATE_COOLDOWN)
  return remaining == 0, remaining
def is_valid_phrase(text):
  if text.startswith("!"):
    return False
  if "\n" in text:
    return False
  words = text.split()
  return 2 <= len(words) <= 12


def remix_phrase(a, b):
  wa = a.split()
  wb = b.split()
  cut = random.randint(1, min(len(wa), len(wb)) - 1)
  return " ".join(wa[:cut] + wb[cut:])


def _clean_display_name(name):
  return re.sub(r"^\[\$?\d+\]\s*", "", name)


async def update_cash_nick(member, cash):
  if member is None or not isinstance(member, discord.Member):
    return

  if member.guild is None:
    return

  cleaned = _clean_display_name(member.display_name)
  prefix = f"[${cash}] "
  max_name_len = max(1, 32 - len(prefix))
  new_nick = f"{prefix}{cleaned[:max_name_len]}"

  if member.nick == new_nick:
    return

  try:
    await member.edit(nick=new_nick, reason="Cash display update")
  except discord.Forbidden:
    debug(f"No permission to edit nickname for {member.display_name}")
  except discord.HTTPException:
    debug(f"Failed to edit nickname for {member.display_name}")


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


def is_money_admin(uid):
  return int(uid) == MONEY_ADMIN_USER_ID


async def set_cash(uid, amount, member=None):
  uid = int(uid)
  user_cash[uid] = max(0, int(amount))
  if member is not None:
    await update_cash_nick(member, user_cash[uid])
  await save_cash_data()


async def load_cash_data():
  if not os.path.exists(CASH_FILE):
    return

  async with aiofiles.open(CASH_FILE, "r", encoding="utf-8") as f:
    raw = await f.read()
    if not raw.strip():
      return

    try:
      data = json.loads(raw)
    except json.JSONDecodeError:
      debug("cash_data.json is invalid; starting fresh")
      return

  loaded_cash = data.get("cash", {})
  for uid, amount in loaded_cash.items():
    try:
      user_cash[int(uid)] = max(0, int(amount))
    except (TypeError, ValueError):
      continue

  loaded_beg = data.get("last_beg", {})
  for uid, ts in loaded_beg.items():
    try:
      last_beg[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_work = data.get("last_work", {})
  for uid, ts in loaded_work.items():
    try:
      last_work[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_pray = data.get("last_pray", {})
  for uid, ts in loaded_pray.items():
    try:
      last_pray[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_tax = data.get("last_tax", {})
  for uid, ts in loaded_tax.items():
    try:
      last_tax[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_debt = data.get("debt", {})
  for uid, amount in loaded_debt.items():
    try:
      user_debt[int(uid)] = max(0, int(amount))
    except (TypeError, ValueError):
      continue

  loaded_loan = data.get("last_loan", {})
  for uid, ts in loaded_loan.items():
    try:
      last_loan[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_debt_penalty = data.get("last_debt_penalty", {})
  for uid, ts in loaded_debt_penalty.items():
    try:
      last_debt_penalty[int(uid)] = int(ts)
    except (TypeError, ValueError):
      continue

  loaded_bot_stats = data.get("bot_stats", {})
  for key in bot_stats.keys():
    try:
      bot_stats[key] = int(loaded_bot_stats.get(key, bot_stats[key]))
    except (TypeError, ValueError):
      continue

  global CHANNEL_ID
  loaded_channel_id = data.get("channel_id")
  if loaded_channel_id is not None:
    try:
      CHANNEL_ID = int(loaded_channel_id)
    except (TypeError, ValueError):
      pass

  debug("Cash data loaded")


async def save_cash_data():
  payload = {
    "cash": {str(uid): amount for uid, amount in user_cash.items()},
    "debt": {str(uid): amount for uid, amount in user_debt.items()},
    "last_beg": {str(uid): ts for uid, ts in last_beg.items()},
    "last_work": {str(uid): ts for uid, ts in last_work.items()},
    "last_pray": {str(uid): ts for uid, ts in last_pray.items()},
    "last_loan": {str(uid): ts for uid, ts in last_loan.items()},
    "last_debt_penalty": {str(uid): ts for uid, ts in last_debt_penalty.items()},
    "last_tax": {str(uid): ts for uid, ts in last_tax.items()},
    "bot_stats": bot_stats,
    "channel_id": CHANNEL_ID,
  }
  async with aiofiles.open(CASH_FILE, "w", encoding="utf-8") as f:
    await f.write(json.dumps(payload, ensure_ascii=True, indent=2))


def get_remaining_cooldown(last_used_ts, cooldown_seconds):
  now = int(time.time())
  elapsed = now - int(last_used_ts)
  remaining = cooldown_seconds - elapsed
  return max(0, remaining)


def fmt_seconds(seconds):
  minutes = seconds // 60
  secs = seconds % 60
  if minutes > 0:
    return f"{minutes}m {secs}s"
  return f"{secs}s"


def tax_rate_for_balance(balance):
  for threshold, rate in TAX_BRACKETS:
    if balance >= threshold:
      return rate
  return 0.0


async def apply_tax_if_due(uid, member=None):
  uid = int(uid)
  remaining = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)
  if remaining > 0:
    return 0, 0.0

  balance = get_cash(uid)
  rate = tax_rate_for_balance(balance)
  tax_amount = int(balance * rate)
  last_tax[uid] = int(time.time())

  if tax_amount > 0:
    await set_cash(uid, balance - tax_amount, member)
  else:
    await save_cash_data()

  return tax_amount, rate


async def apply_debt_penalty_if_due(uid, member=None):
  uid = int(uid)
  debt = get_debt(uid)
  if debt <= 0:
    return 0, 0, 0

  now = int(time.time())
  anchor = last_debt_penalty.get(uid, now)
  elapsed = now - anchor
  ticks = elapsed // DEBT_PENALTY_INTERVAL_SECONDS
  if ticks <= 0:
    return 0, 0, 0

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
  await save_cash_data()
  return total_cash_fee, total_debt_added, int(ticks)


async def terminal_input_loop():
  global CHANNEL_ID
  await bot.wait_until_ready()
  channel = bot.get_channel(CHANNEL_ID)

  if channel is None:
    print("[TERMINAL] Channel not found")
    return

  loop = asyncio.get_running_loop()
  print("[TERMINAL] Ready. Commands: /force, /say <msg>")

  while True:
    msg = await loop.run_in_executor(None, input)
    msg = msg.strip()

    if not msg:
      continue

    # ===== TERMINAL COMMANDS =====

    if msg == "/force":
      print("[TERMINAL] Forcing reply")
      await send_phrase_reply(channel)
      continue

    if msg.startswith("/say "):
      await channel.send(msg[5:])
      continue

    # ===== DEFAULT: SEND RAW =====

    await channel.send(msg)


async def get_recent_human_members(channel, max_messages=60):
  members = {}

  async for msg in channel.history(limit=max_messages):
    author = msg.author
    if getattr(author, "bot", False):
      continue
    if bot_user_id is not None and author.id == bot_user_id:
      continue
    members[author.id] = author

  return list(members.values())


async def bot_economy_loop():
  await bot.wait_until_ready()
  channel = bot.get_channel(CHANNEL_ID)

  if channel is None:
    print("[BOT AUTO] Channel not found")
    return

  while True:
    await asyncio.sleep(random.randint(BOT_AUTO_MIN_DELAY, BOT_AUTO_MAX_DELAY))

    if not BOT_AUTO_ECONOMY_ENABLED:
      continue

    if random.random() > BOT_AUTO_TRIGGER_CHANCE:
      continue

    if bot_user_id is None:
      continue

    guild = getattr(channel, "guild", None)
    bot_member = guild.get_member(bot_user_id) if guild is not None else None

    available_actions = []
    recent_targets = []
    if get_remaining_cooldown(last_beg.get(bot_user_id, 0), BEG_COOLDOWN) == 0:
      available_actions.append("beg")
    if get_remaining_cooldown(last_work.get(bot_user_id, 0), WORK_COOLDOWN) == 0:
      available_actions.append("work")
    if get_bot_cash() > 0:
      available_actions.append("gamble")

    if get_bot_cash() >= BOT_MIN_BALANCE_FOR_SOCIAL and random.random() < BOT_SOCIAL_ACTION_CHANCE:
      recent_targets = await get_recent_human_members(channel)
      if recent_targets:
        available_actions.append("give")
        available_actions.append("steal")

    if not available_actions:
      continue

    action = random.choice(available_actions)

    if action == "beg":
      reward = random.randint(BEG_MIN, BEG_MAX)
      last_beg[bot_user_id] = int(time.time())
      await channel.send("!beg")
      await set_cash(bot_user_id, get_bot_cash() + reward, bot_member)
      await channel.send(f"bot used !beg and got ${reward}. bot cash: ${get_bot_cash()}")
      continue

    if action == "work":
      reward = random.randint(WORK_MIN, WORK_MAX)
      last_work[bot_user_id] = int(time.time())
      await channel.send("!work")
      await set_cash(bot_user_id, get_bot_cash() + reward, bot_member)
      await channel.send(f"bot used !work and earned ${reward}. bot cash: ${get_bot_cash()}")
      continue

    if action == "give":
      if not recent_targets:
        continue

      target = random.choice(recent_targets)
      balance = get_bot_cash()
      if balance <= 0:
        continue

      give_amount = min(balance, random.randint(BOT_GIVE_MIN, BOT_GIVE_MAX))
      if give_amount <= 0:
        continue

      await channel.send(f"!give {target.mention} {give_amount}")
      target_balance = get_cash(target.id)
      await set_cash(bot_user_id, balance - give_amount, bot_member)
      await set_cash(target.id, target_balance + give_amount, target if isinstance(target, discord.Member) else None)
      bot_stats["given"] += give_amount
      await save_cash_data()
      await channel.send(
        f"bot gave ${give_amount} to {target.mention}. "
        f"balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}"
      )
      continue

    if action == "steal":
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

      await channel.send(f"!steal {target.mention} {steal_amount}")
      success = random.random() < STEAL_SUCCESS_CHANCE

      if success:
        bot_stats["steal_success"] += 1
        await set_cash(bot_user_id, thief_balance + steal_amount, bot_member)
        await set_cash(target.id, target_balance - steal_amount, target if isinstance(target, discord.Member) else None)
        await save_cash_data()
        await channel.send(
          f"bot steal success: took ${steal_amount} from {target.mention}. "
          f"balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}"
        )
        continue

      penalty = max(1, int(steal_amount * STEAL_FAIL_PENALTY_RATE))
      penalty = min(penalty, thief_balance)
      bot_stats["steal_fail"] += 1

      if penalty > 0:
        await set_cash(bot_user_id, thief_balance - penalty, bot_member)
        await set_cash(target.id, target_balance + penalty, target if isinstance(target, discord.Member) else None)
        await save_cash_data()
        await channel.send(
          f"bot steal failed: paid ${penalty} to {target.mention}. "
          f"balances: bot ${get_bot_cash()}, them ${get_cash(target.id)}"
        )
      else:
        await save_cash_data()
        await channel.send("bot steal failed, but had no money for penalty")
      continue

    # gamble
    balance = get_bot_cash()
    if balance <= 0:
      continue

    bet = min(balance, random.randint(BOT_GAMBLE_BET_MIN, BOT_GAMBLE_BET_MAX))
    if bet <= 0:
      continue

    await channel.send(f"!gamble {bet}")
    won = random.random() < GAMBLE_WIN_CHANCE
    new_balance = balance + bet if won else balance - bet
    await set_cash(bot_user_id, new_balance, bot_member)

    if won:
      bot_stats["gamble_wins"] += 1
      await save_cash_data()
      await channel.send(f"bot won ${bet}. bot cash: ${new_balance}")
    else:
      bot_stats["gamble_losses"] += 1
      await save_cash_data()
      await channel.send(f"bot lost ${bet}. bot cash: ${new_balance}")

def learn_reactions(text):
  words = text.split()
  if len(words) < 3:
    return

  reaction_starts.append(words[0])
  reaction_ends.append(words[-1])
  reaction_middles.append(" ".join(words[1:-1]))

  if len(reaction_starts) > MAX_REACTIONS:
    reaction_starts.pop(0)
    reaction_middles.pop(0)
    reaction_ends.pop(0)

  debug("Learned reaction pattern")


def generate_learned_reaction():
  if not reaction_starts or not reaction_ends:
    debug("Reaction generation failed: insufficient data")
    return None

  start = random.choice(reaction_starts)
  end = random.choice(reaction_ends)
  middle = ""

  if reaction_middles and random.random() < 0.7:
    middle = " " + random.choice(reaction_middles)

  return f"{start}{middle} {end}".strip()


async def append_corpus_line(uid, text, is_quote=False):
  payload = text.strip()
  if not payload:
    return

  if is_quote:
    payload = f"{CORPUS_QUOTE_PREFIX}{payload}"

  async with aiofiles.open(TEXT_FILE, "a", encoding="utf-8") as f:
    await f.write(f"{int(uid)}::{payload}\n")


async def load_corpus():
  if not os.path.exists(TEXT_FILE):
    return

  async with aiofiles.open(TEXT_FILE, "r", encoding="utf-8") as f:
    async for line in f:
      line = line.strip()
      if "::" not in line:
        continue
      uid, phrase = line.split("::", 1)
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
      # Keep track-mode imitation corpus-backed across restarts.
      user_full_lines.setdefault(uid, []).append(phrase)

      if len(user_full_lines[uid]) > MAX_TRACK_LINES:
        user_full_lines[uid].pop(0)

  debug("Corpus loaded")


# ================= REPLY LOGIC =================


async def send_phrase_reply(channel):
  if random.random() < SILENCE_CHANCE:
    debug("Silence roll triggered")
    return

  # In TRACK mode, imitate using full lines from the tracked user only.
  if mode == "track":
    source_pool = user_full_lines.get(track_target, [])[-MAX_RECENT_PHRASES:]
    if not source_pool:
      # Fallback to corpus-loaded phrase pool for the tracked user.
      source_pool = user_pools.get(track_target, [])[-MAX_RECENT_PHRASES:]
    debug(f"Using TRACK full-line pool ({len(source_pool)})")

    if not source_pool:
      debug("No tracked full lines available")
      return

    sentence = random.choice(source_pool)
    debug("Reply type: full line echo")
  else:
    source_pool = []
    for phrases in user_pools.values():
      source_pool.extend(phrases[-MAX_RECENT_PHRASES:])
    debug(f"Using GLOBAL pool ({len(source_pool)})")

    if not source_pool:
      sentence = random.choice(FALLBACKS)
      debug("Using fallback")
    else:
      roll = random.random()
      debug(f"Reply roll: {roll:.2f}")

      if roll < 0.25:
        sentence = random.choice(source_pool)
        debug("Reply type: direct echo")

      elif roll < 0.5:
        sentence = generate_learned_reaction() or random.choice(source_pool)
        debug("Reply type: learned reaction")

      elif roll < 0.8:
        count = random.randint(2, MAX_REPLY_PHRASES)
        parts = random.sample(source_pool, min(count, len(source_pool)))
        sentence = " ".join(parts)
        debug(f"Reply type: mash ({count})")

      else:
        if len(source_pool) >= 2:
          a, b = random.sample(source_pool, 2)
          sentence = remix_phrase(a, b)
          debug("Reply type: remix")
        else:
          sentence = source_pool[0]

  if sentence in recent_sentences:
    debug("Sentence rejected (recent duplicate)")
    return

  recent_sentences.append(sentence)
  if len(recent_sentences) > MAX_RECENT_SENTENCES:
    recent_sentences.pop(0)

  debug(f"Sending: {sentence}")
  bot_stats["replies_sent"] += 1
  await save_cash_data()
  await channel.send(sentence)


# ================= EVENTS =================


@bot.event
async def on_ready():
  global bot_user_id
  await load_corpus()
  await load_cash_data()
  bot_user_id = bot.user.id
  get_cash(bot_user_id)
  await save_cash_data()
  print(f"{bot.user} has connected to Discord!")
  try:
    synced = await bot.tree.sync()
    print(f"Synced {len(synced)} command(s)")
  except Exception as e:
    print(f"Failed to sync commands: {e}")
  bot.loop.create_task(terminal_input_loop())
  bot.loop.create_task(bot_economy_loop())

@bot.event
async def on_message(message):
  global message_counter, messages_per_reply

  if message.author.bot or message.channel.id != CHANNEL_ID:
    return

  raw_content = message.content.strip()
  content = raw_content.lower()
  uid = message.author.id

  get_cash(uid)
  debt_fee, debt_growth, debt_ticks = await apply_debt_penalty_if_due(uid, message.author)
  taxed, rate = await apply_tax_if_due(uid, message.author)
  bot_stats["messages_seen"] += 1

  if debt_ticks > 0:
    await message.channel.send(
      f"{message.author.mention} overdue loan penalty x{debt_ticks}: -${debt_fee} cash, +${debt_growth} debt. "
      f"cash: ${get_cash(uid)} | debt: ${get_debt(uid)}"
    )

  if taxed > 0:
    if bot_user_id is not None:
      await set_cash(bot_user_id, get_bot_cash() + taxed)
      bot_stats["tax_collected"] += taxed
    await message.channel.send(
      f"{message.author.mention} paid ${taxed} tax ({int(rate * 100)}%). new balance: ${get_cash(uid)}"
    )

  debug(f"Message from {message.author.display_name}: {content}")
  debug(f"Mode: {mode}")

  if mode == "track" and uid == track_target and raw_content and not raw_content.startswith("!"):
    user_full_lines.setdefault(uid, []).append(raw_content)
    if len(user_full_lines[uid]) > MAX_TRACK_LINES:
      user_full_lines[uid].pop(0)

  if is_valid_phrase(content):
    debug("Phrase accepted")
    learn_reactions(content)

    if mode == "global" or (mode == "track" and uid == track_target):
      user_pools.setdefault(uid, []).append(content)
      if len(user_pools[uid]) > MAX_PHRASES:
        user_pools[uid].pop(0)

      await append_corpus_line(uid, content, is_quote=False)
  else:
    debug("Phrase rejected")

  message_counter += 1
  debug(f"Message counter: {message_counter}/{messages_per_reply}")

  if message_counter >= messages_per_reply:
    message_counter = 0
    messages_per_reply = random.randint(1, 5)
    debug(f"Trigger reply, next in {messages_per_reply}")
    await send_phrase_reply(message.channel)

  await bot.process_commands(message)


# ================= COMMANDS =================

@bot.command()
async def rick(ctx):
  if ctx.channel.id == CHANNEL_ID:
    debug("ricked")
    await ctx.send("We're no strangers to love\nYou know the rules and so do I\nA full commitment's what I'm thinking of\nYou wouldn't get this from any other guy\nI just wanna tell you how I'm feeling\nGotta make you understand Never gonna give you up\nNever gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye Never gonna tell a lie and hurt you We've known each other for so long your heart's been aching but you're too shy to say it Inside we both know what's been going on We know the game and we're gonna play it And if you ask me how I'm feeling Don't tell me you're too blind to see\nNever gonna give you up\nNever gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye\nNever gonna tell a lie and hurt you\nNever gonna give you up Never gonna let you down\nNever gonna run around and desert you\nNever gonna make you cry\nNever gonna say goodbye Never gonna tell a lie and hurt you Never gonna give, never gonna give (Give you up)\nWe've known each other for so long your heart's been aching but you're too shy to say it Inside we both know what's been going on We know the game and we're gonna play it And if you ask me how I'm feeling Don't tell me you're too blind to see Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye Never gonna tell a lie and hurt you Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye Never gonna tell a lie and hurt you Never gonna give you up Never gonna let you down Never gonna run around and desert you Never gonna make you cry Never gonna say goodbye")
@bot.command()
async def force(ctx):
  if ctx.channel.id == CHANNEL_ID:
    debug("Force command used")
    await send_phrase_reply(ctx.channel)
@bot.command(name="assassinate")
async def assassinate(ctx, member: discord.Member):
    if ctx.channel.id != CHANNEL_ID:
        return

    attacker_id = ctx.author.id
    target_id = member.id

    if attacker_id == target_id:
        await ctx.send("You can't assassinate yourself. Try therapy instead.")
        return

    can_use, remaining = can_use_assassinate(attacker_id)
    if not can_use:
        await ctx.send(f"Assassinate is on cooldown. Try again in {fmt_seconds(remaining)}.")
        return

    attacker_cash = get_cash(attacker_id)
    if attacker_cash < ASSASSINATE_COST:
        await ctx.send(f"You need ${ASSASSINATE_COST} to attempt an assassination. Current cash: ${attacker_cash}")
        return

    # Deduct the cost
    await set_cash(attacker_id, attacker_cash - ASSASSINATE_COST, ctx.author)
    last_assassinate[attacker_id] = int(time.time())

    success = random.random() < ASSASSINATE_SUCCESS_CHANCE
    if success:
        # On success, target loses all cash and gains debt
        target_cash = get_cash(target_id)
        user_cash[target_id] = 0
        user_debt[target_id] = get_debt(target_id) + 10000
        await update_cash_nick(member, 0)
        await save_cash_data()
        await ctx.send(f"💀 Assassination succeeded! {member.mention} loses ${target_cash} and gains $10,000 debt.")
    else:
        # On fail, attacker loses all cash and gains debt
        user_cash[attacker_id] = 0
        user_debt[attacker_id] = get_debt(attacker_id) + 10000
        await update_cash_nick(ctx.author, 0)
        await save_cash_data()
        await ctx.send(f"❌ Assassination failed! {ctx.author.mention} loses all cash and gains $10,000 debt.")

@bot.command()
async def reset(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return
  user_pools.clear()
  user_full_lines.clear()
  user_quotes.clear()
  recent_sentences.clear()
  user_cash.clear()
  user_debt.clear()
  last_beg.clear()
  last_work.clear()
  last_pray.clear()
  last_loan.clear()
  last_debt_penalty.clear()
  last_tax.clear()
  for key in bot_stats.keys():
    bot_stats[key] = 0
  async with aiofiles.open(TEXT_FILE, "w", encoding="utf-8") as f:
    await f.write("")
  async with aiofiles.open(CASH_FILE, "w", encoding="utf-8") as f:
    await f.write("{}")
  await ctx.send("memory wiped")
  debug("Memory reset")


@bot.command()
async def cash(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  balance = get_cash(ctx.author.id)
  await update_cash_nick(ctx.author, balance)
  await ctx.send(f"{ctx.author.mention} has ${balance}")


@bot.command()
async def stats(ctx, member: discord.Member = None):
  if ctx.channel.id != CHANNEL_ID:
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
    debt_penalty_cd = get_remaining_cooldown(
      last_debt_penalty.get(uid, int(time.time())),
      DEBT_PENALTY_INTERVAL_SECONDS,
    )
    debt_penalty_text = fmt_seconds(debt_penalty_cd)
  else:
    debt_penalty_text = "none"

  embed = discord.Embed(
    title=f"stats: {target.display_name}",
    color=discord.Color.green(),
  )
  embed.add_field(name="cash", value=f"${cash}", inline=True)
  embed.add_field(name="debt", value=f"${debt}", inline=True)
  embed.add_field(name="loan status", value="active" if debt > 0 else "clear", inline=True)
  embed.add_field(name="beg cooldown", value=fmt_seconds(beg_cd), inline=True)
  embed.add_field(name="work cooldown", value=fmt_seconds(work_cd), inline=True)
  embed.add_field(name="pray cooldown", value=fmt_seconds(pray_cd), inline=True)
  embed.add_field(name="loan cooldown", value=fmt_seconds(loan_cd), inline=True)
  embed.add_field(name="tax due in", value=fmt_seconds(tax_cd), inline=True)
  embed.add_field(name="debt penalty in", value=debt_penalty_text, inline=True)
  await ctx.send(embed=embed)


@bot.command()
async def setcash(ctx, member: discord.Member, amount: int):
  if ctx.channel.id != CHANNEL_ID:
    return

  if not is_money_admin(ctx.author.id):
    await ctx.send("not allowed")
    return

  await set_cash(member.id, amount, member)
  await ctx.send(f"set {member.mention} cash to ${get_cash(member.id)}")


@bot.command()
async def addcash(ctx, member: discord.Member, amount: int):
  if ctx.channel.id != CHANNEL_ID:
    return

  if not is_money_admin(ctx.author.id):
    await ctx.send("not allowed")
    return

  if amount <= 0:
    await ctx.send("amount must be more than 0")
    return

  await set_cash(member.id, get_cash(member.id) + amount, member)
  await ctx.send(f"added ${amount} to {member.mention}. new cash: ${get_cash(member.id)}")


@bot.command()
async def takecash(ctx, member: discord.Member, amount: int):
  if ctx.channel.id != CHANNEL_ID:
    return

  if not is_money_admin(ctx.author.id):
    await ctx.send("not allowed")
    return

  if amount <= 0:
    await ctx.send("amount must be more than 0")
    return

  await set_cash(member.id, get_cash(member.id) - amount, member)
  await ctx.send(f"took ${amount} from {member.mention}. new cash: ${get_cash(member.id)}")


@bot.command()
async def gamble(ctx, amount: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  balance = get_cash(ctx.author.id)

  if amount.lower() == "all":
    bet = balance
  else:
    try:
      bet = int(amount)
    except ValueError:
      await ctx.send("use a number or 'all' (example: !gamble 200)")
      return

  if bet <= 0:
    await ctx.send("bet must be more than 0")
    return

  if bet > balance:
    await ctx.send("you don't have that much cash")
    return

  won = random.random() < GAMBLE_WIN_CHANCE
  new_balance = balance + bet if won else balance - bet
  await set_cash(ctx.author.id, new_balance, ctx.author)

  if won:
    bot_stats["gamble_wins"] += 1
    await save_cash_data()
    await ctx.send(f"you won ${bet}. new balance: ${new_balance}")
  else:
    bot_stats["gamble_losses"] += 1
    await save_cash_data()
    await ctx.send(f"you lost ${bet}. new balance: ${new_balance}")


@bot.command()
async def beg(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  current_cash = get_cash(uid)
  remaining = get_remaining_cooldown(last_beg.get(uid, 0), BEG_COOLDOWN)
  if remaining > 0:
    await ctx.send(f"you can beg again in {fmt_seconds(remaining)}")
    return

  reward = random.randint(BEG_MIN, BEG_MAX)
  last_beg[uid] = int(time.time())
  await set_cash(uid, current_cash + reward, ctx.author)
  await ctx.send(f"someone gave you ${reward}. new balance: ${get_cash(uid)}")


@bot.command()
async def work(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  current_cash = get_cash(uid)
  remaining = get_remaining_cooldown(last_work.get(uid, 0), WORK_COOLDOWN)
  if remaining > 0:
    await ctx.send(f"you can work again in {fmt_seconds(remaining)}")
    return

  reward = random.randint(WORK_MIN, WORK_MAX)
  last_work[uid] = int(time.time())
  await set_cash(uid, current_cash + reward, ctx.author)
  await ctx.send(f"you worked a shift and earned ${reward}. new balance: ${get_cash(uid)}")


@bot.command()
async def pray(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  remaining = get_remaining_cooldown(last_pray.get(uid, 0), PRAY_COOLDOWN)
  if remaining > 0:
    await ctx.send(f"you can pray to jachlam again in {fmt_seconds(remaining)}")
    return

  last_pray[uid] = int(time.time())
  if random.random() < PRAY_SUCCESS_CHANCE:
    reward = random.randint(PRAY_MIN, PRAY_MAX)
    await set_cash(uid, get_cash(uid) + reward, ctx.author)
    await ctx.send(
      f"you prayed to jachlam and were blessed with ${reward}. new balance: ${get_cash(uid)}"
    )
    return

  await save_cash_data()
  await ctx.send("you prayed to jachlam, but received no blessing this time")


@bot.command()
async def debt(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  debt_amount = get_debt(uid)
  if debt_amount <= 0:
    await ctx.send(f"{ctx.author.mention} debt: $0 | cash: ${get_cash(uid)}")
    return

  remaining = get_remaining_cooldown(
    last_debt_penalty.get(uid, int(time.time())),
    DEBT_PENALTY_INTERVAL_SECONDS,
  )
  await ctx.send(
    f"{ctx.author.mention} debt: ${debt_amount} | cash: ${get_cash(uid)} | "
    f"next overdue penalty in {fmt_seconds(remaining)}"
  )


@bot.command()
async def loan(ctx, amount: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  existing_debt = get_debt(uid)
  if existing_debt > 0:
    await ctx.send(f"pay your current debt first with !repay. debt: ${existing_debt}")
    return

  remaining = get_remaining_cooldown(last_loan.get(uid, 0), LOAN_COOLDOWN)
  if remaining > 0:
    await ctx.send(f"you can take another loan in {fmt_seconds(remaining)}")
    return

  try:
    principal = int(amount)
  except ValueError:
    await ctx.send(f"use a number between {LOAN_MIN} and {LOAN_MAX} (example: !loan 500)")
    return

  if principal < LOAN_MIN or principal > LOAN_MAX:
    await ctx.send(f"loan must be between ${LOAN_MIN} and ${LOAN_MAX}")
    return

  debt_total = principal + max(1, int(principal * LOAN_INTEREST_RATE))
  last_loan[uid] = int(time.time())
  last_debt_penalty[uid] = int(time.time())
  user_debt[uid] = debt_total
  await set_cash(uid, get_cash(uid) + principal, ctx.author)
  await save_cash_data()
  await ctx.send(
    f"loan approved: +${principal} cash. total debt is ${debt_total} (includes {int(LOAN_INTEREST_RATE * 100)}% interest)"
  )


@bot.command()
async def repay(ctx, amount: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  current_debt = get_debt(uid)
  if current_debt <= 0:
    await ctx.send("you have no debt")
    return

  balance = get_cash(uid)
  if balance <= 0:
    await ctx.send("you have no cash to repay with")
    return

  if amount.lower() == "all":
    payment = min(balance, current_debt)
  else:
    try:
      payment = int(amount)
    except ValueError:
      await ctx.send("use a number or 'all' (example: !repay 300)")
      return

  if payment <= 0:
    await ctx.send("repay amount must be more than 0")
    return

  payment = min(payment, balance, current_debt)
  user_debt[uid] = current_debt - payment
  if user_debt[uid] <= 0:
    user_debt[uid] = 0
    last_debt_penalty.pop(uid, None)
  await set_cash(uid, balance - payment, ctx.author)
  await save_cash_data()

  if user_debt[uid] == 0:
    await ctx.send(f"debt fully repaid. remaining cash: ${get_cash(uid)}")
  else:
    await ctx.send(f"paid ${payment}. remaining debt: ${user_debt[uid]} | cash: ${get_cash(uid)}")


@bot.command()
async def give(ctx, member: discord.Member, amount: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  giver_id = ctx.author.id
  receiver_id = member.id

  if giver_id == receiver_id:
    await ctx.send("you can't give money to yourself")
    return

  giver_balance = get_cash(giver_id)

  if amount.lower() == "all":
    transfer = giver_balance
  else:
    try:
      transfer = int(amount)
    except ValueError:
      await ctx.send("use a number or 'all' (example: !give @user 200)")
      return

  if transfer <= 0:
    await ctx.send("amount must be more than 0")
    return

  if transfer > giver_balance:
    await ctx.send("you don't have that much cash")
    return

  receiver_balance = get_cash(receiver_id)
  await set_cash(giver_id, giver_balance - transfer, ctx.author)
  await set_cash(receiver_id, receiver_balance + transfer, member)
  bot_stats["given"] += transfer
  if bot_user_id is not None and receiver_id == bot_user_id:
    bot_stats["received"] += transfer
  await save_cash_data()
  await ctx.send(
    f"{ctx.author.mention} gave ${transfer} to {member.mention}. "
    f"balances: you ${get_cash(giver_id)}, them ${get_cash(receiver_id)}"
  )


@bot.command()
async def steal(ctx, member: discord.Member, amount: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  thief_id = ctx.author.id
  target_id = member.id

  if thief_id == target_id:
    await ctx.send("you can't steal from yourself")
    return

  thief_balance = get_cash(thief_id)
  target_balance = get_cash(target_id)

  if target_balance <= 0:
    await ctx.send("that user has no money to steal")
    return

  if amount.lower() == "all":
    requested = target_balance
  else:
    try:
      requested = int(amount)
    except ValueError:
      await ctx.send("use a number or 'all' (example: !steal @user 150)")
      return

  if requested <= 0:
    await ctx.send("amount must be more than 0")
    return

  steal_amount = min(requested, target_balance)
  success = random.random() < STEAL_SUCCESS_CHANCE

  if success:
    bot_stats["steal_success"] += 1
    await set_cash(thief_id, thief_balance + steal_amount, ctx.author)
    await set_cash(target_id, target_balance - steal_amount, member)
    await save_cash_data()
    await ctx.send(
      f"steal success: {ctx.author.mention} stole ${steal_amount} from {member.mention}. "
      f"balances: you ${get_cash(thief_id)}, them ${get_cash(target_id)}"
    )
    return

  penalty = max(1, int(steal_amount * STEAL_FAIL_PENALTY_RATE))
  penalty = min(penalty, thief_balance)

  if penalty > 0:
    bot_stats["steal_fail"] += 1
    await set_cash(thief_id, thief_balance - penalty, ctx.author)
    await set_cash(target_id, target_balance + penalty, member)
    await save_cash_data()
    await ctx.send(
      f"steal failed: you paid ${penalty} to {member.mention}. "
      f"balances: you ${get_cash(thief_id)}, them ${get_cash(target_id)}"
    )
  else:
    bot_stats["steal_fail"] += 1
    await save_cash_data()
    await ctx.send("steal failed, but you had no money for a penalty")


@bot.command()
async def botstats(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  await ctx.send(
    "\n".join([
      f"bot cash: ${get_bot_cash()}",
      f"messages seen: {bot_stats['messages_seen']}",
      f"replies sent: {bot_stats['replies_sent']}",
      f"tax collected: ${bot_stats['tax_collected']}",
      f"gamble W/L: {bot_stats['gamble_wins']}/{bot_stats['gamble_losses']}",
      f"steal S/F: {bot_stats['steal_success']}/{bot_stats['steal_fail']}",
      f"given/received: ${bot_stats['given']}/${bot_stats['received']}",
    ])
  )


@bot.command()
async def taxinfo(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  uid = ctx.author.id
  balance = get_cash(uid)
  rate = tax_rate_for_balance(balance)
  remaining = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)

  if remaining > 0:
    await ctx.send(
      f"{ctx.author.mention} tax bracket: {int(rate * 100)}% on ${balance}. next tax in {fmt_seconds(remaining)}"
    )
  else:
    await ctx.send(
      f"{ctx.author.mention} tax bracket: {int(rate * 100)}% on ${balance}. tax is due now"
    )


@bot.command()
async def quote(ctx, member: discord.Member = None):
  if ctx.channel.id != CHANNEL_ID:
    return

  if member is not None:
    pool = user_quotes.get(member.id, [])
    if not pool:
      await ctx.send(f"no quotes saved for {member.mention}")
      return
    await ctx.send(f"{member.mention}: \"{random.choice(pool)}\"")
    return

  all_quotes = []
  for quotes in user_quotes.values():
    all_quotes.extend(quotes)

  if not all_quotes:
    await ctx.send("no quotes saved yet")
    return

  await ctx.send(f"\"{random.choice(all_quotes)}\"")


@bot.command()
async def quoteadd(ctx, *, text: str):
  if ctx.channel.id != CHANNEL_ID:
    return

  phrase = text.strip()
  if not phrase:
    await ctx.send("usage: !quoteadd <text>")
    return

  uid = ctx.author.id
  user_quotes.setdefault(uid, []).append(phrase)
  await append_corpus_line(uid, phrase, is_quote=True)
  await ctx.send("quote saved")


@bot.command()
async def quotereply(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  ref = ctx.message.reference
  if ref is None or ref.message_id is None:
    await ctx.send("reply to a message, then use !quotereply")
    return

  try:
    if isinstance(ref.resolved, discord.Message):
      target_message = ref.resolved
    else:
      target_message = await ctx.channel.fetch_message(ref.message_id)
  except (discord.NotFound, discord.Forbidden, discord.HTTPException):
    await ctx.send("could not find that replied message")
    return

  phrase = target_message.content.strip()
  if not phrase:
    await ctx.send("that message has no text to quote")
    return

  uid = target_message.author.id
  user_quotes.setdefault(uid, []).append(phrase)
  await append_corpus_line(uid, phrase, is_quote=True)
  await ctx.send(f"quote saved for {target_message.author.mention}")


@bot.command()
async def quotes(ctx, member: discord.Member = None, page: int = 1):
  if ctx.channel.id != CHANNEL_ID:
    return

  page = max(1, page)

  if member is not None:
    entries = [(member.id, quote_text) for quote_text in user_quotes.get(member.id, [])]
    title = f"quotes for {member.display_name}"
  else:
    entries = []
    for uid, quote_list in user_quotes.items():
      for quote_text in quote_list:
        entries.append((uid, quote_text))
    title = "all quotes"

  if not entries:
    await ctx.send("no quotes saved yet")
    return

  total_pages = max(1, (len(entries) + QUOTES_PAGE_SIZE - 1) // QUOTES_PAGE_SIZE)
  if page > total_pages:
    await ctx.send(f"page out of range. max page is {total_pages}")
    return

  start = (page - 1) * QUOTES_PAGE_SIZE
  end = min(start + QUOTES_PAGE_SIZE, len(entries))
  lines = []

  for i, (uid, quote_text) in enumerate(entries[start:end], start=start + 1):
    safe_text = quote_text.replace("\n", " ").strip()
    if len(safe_text) > 180:
      safe_text = safe_text[:177] + "..."

    if member is None:
      guild_member = ctx.guild.get_member(uid) if ctx.guild is not None else None
      author_name = guild_member.display_name if guild_member is not None else f"user {uid}"
      lines.append(f"{i}. **{author_name}**: \"{safe_text}\"")
    else:
      lines.append(f"{i}. \"{safe_text}\"")

  embed = discord.Embed(
    title=title,
    description="\n".join(lines),
    color=discord.Color.blue(),
  )
  embed.set_footer(text=f"page {page}/{total_pages} • total quotes: {len(entries)}")
  await ctx.send(embed=embed)

@bot.command()
async def ping(ctx):
    if ctx.channel.id != CHANNEL_ID:
        return

    user_id = 1162994221280669738

    for i in range(20):  # number of pings
        await ctx.send(f"<@{user_id}>")
        await asyncio.sleep(0.8)  # delay so Discord doesn’t slap your bot
@bot.command()
async def forcetaxall(ctx):
  if ctx.channel.id != CHANNEL_ID:
    return

  if not is_money_admin(ctx.author.id):
    await ctx.send("not allowed")
    return

  total_collected = 0
  users_taxed = 0
  
  for uid in list(user_cash.keys()):
    # Reset the last_tax timestamp to force tax
    last_tax[uid] = 0
    tax_amount, rate = await apply_tax_if_due(uid, ctx.guild.get_member(uid))
    users_taxed += 1
    if tax_amount > 0:
      total_collected += tax_amount
  
  await ctx.send(f"forced tax on {users_taxed} users, collected ${total_collected}")


@bot.command()
async def setup(ctx, channel_id: int = None):
  global CHANNEL_ID
  if not is_money_admin(ctx.author.id):
    await ctx.send("not allowed")
    return

  if channel_id is None:
    await ctx.send(f"current channel: {CHANNEL_ID}. usage: !setup <channel_id>")
    return

  try:
    CHANNEL_ID = channel_id
    await save_cash_data()
    await ctx.send(f"channel ID set to {CHANNEL_ID}")
  except Exception as e:
    await ctx.send(f"error setting channel: {e}")


@bot.command(name="global")
async def global_mode(ctx):
  global mode, track_target
  mode = "global"
  track_target = None
  await ctx.send("back to global mode")
  debug("Switched to GLOBAL")


@bot.command()
@commands.is_owner()
async def imitate(ctx, member: discord.Member):
  global mode, track_target
  mode = "track"
  track_target = member.id
  await ctx.send(f"imitating {member.display_name}")
  debug(f"Switched to TRACK ({member.id})")

  await asyncio.sleep(TRACK_DURATION)

  mode = "global"
  track_target = None
  await ctx.send("imitation ended")
  debug("Track expired")


# ================= RUN =================

if __name__ == "__main__":
  if not TOKEN:
    raise ValueError("No token found. Make sure DISCORD_TOKEN or TOKEN is set in your environment variables.")
  bot.run(TOKEN)
