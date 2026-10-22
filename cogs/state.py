"""Jachlam shared state — pure Python, zero Discord imports.

All mutable runtime state and pure helper functions live here. Command cogs
import from this module only. Discord-dependent helpers (rogue_send, embeds,
task loops, event listeners) live in their respective cogs.
"""

import asyncio
import hashlib
import json
import os
import random
import re
import shutil
import time
import traceback
from collections import Counter, deque
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import aiofiles
from dotenv import load_dotenv

try:
    from PIL import Image, ImageDraw, ImageFont
    GALACTIC_MAP_IMAGE_SUPPORT = True
except Exception:
    Image = ImageDraw = ImageFont = None
    GALACTIC_MAP_IMAGE_SUPPORT = False

load_dotenv()
TOKEN = os.getenv('DISCORD_TOKEN') or os.getenv('TOKEN')
CHANNEL_ID_DEFAULT = 1409844931761279019
MONEY_ADMIN_USER_ID = 1055064009457537024
TEXT_FILE = 'markov_corpus.txt'
CASH_FILE = 'cash_data.json'
INVENTORY_FILE = 'inventory_data.json'
SEEN_GIFS_FILE = 'seen_gifs.json'
DEATH_FILE = 'death_data.json'
EPSTEIN_FILE = 'epstein_data.json'
SILENCE_FILE = 'silence_data.json'
BACKUP_DIR = 'backups'
CLEAN_EXIT_MARKER_FILE = 'clean_exit_restore.json'
JACHLAM_VERSION = '2026.10.16-r40'

# --- Limits / constants ---
MAX_PHRASES = 400
MAX_RECENT_PHRASES = 80
MAX_RECENT_SENTENCES = 15
MAX_REPLY_PHRASES = 3
MAX_TRACK_LINES = 30000
MAX_CORPUS_LINES = 12000
MAX_REACTIONS = 200
SILENCE_CHANCE = 0.3
GALACTIC_MAP_CACHE_SECONDS = 300
PRESENCE_ROTATE_SECONDS = 300
AUTOSAVE_INTERVAL_SECONDS = 300
CHAT_ACTIVITY_WINDOW = 5 * 60
CHAT_ACTIVITY_MAX_EVENTS = 4000
CHAT_ACTIVITY_FRESH_SECONDS = 60
NICK_EDIT_MIN_INTERVAL = 20
TRACK_DURATION = 300

# --- Economy ---
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
DAILY_REPORT_HOUR = 19
TRIAL_VOTE_SECONDS = 30
MAX_WANTED_LEVEL = 5
LAST_DIG_COOLDOWN = 300

# --- Helldivers ---
HELLDIVERS_ASSIGNMENTS_URL = 'https://api.helldivers2.dev/api/v1/assignments'
HELLDIVERS_ASSIGNMENTS_FALLBACK_URL = 'https://helldiverstrainingmanual.com/api/v1/war/major-orders'
HELLDIVERS_PLANETS_URL = 'https://api.helldivers2.dev/api/v1/planets'
HELLDIVERS_CAMPAIGNS_URL = 'https://api.helldivers2.dev/api/v1/campaigns'
HELLDIVERS_FALLBACK_STATUS_URL = 'https://helldiverstrainingmanual.com/api/v1/war/status'
HELLDIVERS_FALLBACK_INFO_URL = 'https://helldiverstrainingmanual.com/api/v1/war/info'
HELLDIVERS_FALLBACK_PLANETS_URL = 'https://helldiverstrainingmanual.com/api/v1/planets'
MAJOR_ORDER_POLL_SECONDS = 600
MAJOR_ORDER_ANNOUNCEMENT_COOLDOWN = 60 * 60
MAJOR_ORDER_PROGRESS_UPDATE_SECONDS = 6 * 60 * 60

# --- Role guard / deadman ---
ROLE_GUARD_USER_ID = 1055064009457537024
ROLE_GUARD_ROLE_ID = 1409844930381090868
ROLE_GUARD_GUILD_ID = 1409844930381090868
LAMJACH_USER_ID = 0
LAMJACH_HEARTBEAT_FILE = 'lamjach_heartbeat'
JACHLAM_IDENTITY_FILE = 'jachlam_identity'
BOT_DISTRESS_FILE = 'bot_distress.json'
DEADMAN_HEARTBEAT_FILE = 'deadman_heartbeat'
DEADMAN_PAUSE_FILE = 'deadman_paused'
ROLE_GUARD_CHECK_SECONDS = 60
BOT_GUARD_CHECK_SECONDS = 60
DEADMAN_HEARTBEAT_SECONDS = 60
SERVER_PUNISH_COOLDOWN = 3600
BOT_GUARD_ALERT_COOLDOWN = 3600
NUKE_TIMEOUT_DAYS = 7
NUKE_CONFIRM_WINDOW = 20
GIF_REPEAT_TIMEOUT_DAYS = 7
EPSTEIN_CHANNEL_ID = 1528950760962789426
ONLINE_WATCH_TARGET_ID = 1330731391629004905
ONLINE_WATCH_NOTIFY_ID = MONEY_ADMIN_USER_ID
ONLINE_WATCH_COOLDOWN = 30 * 60
ORION_USER_ID = 1388459209431187557
ANDY_USER_ID = 1091302334618939422
EXECUTIONER_USER_ID = MONEY_ADMIN_USER_ID

ADMIN_USER_IDS = {MONEY_ADMIN_USER_ID}
PROTECTED_USER_IDS = {1055064009457537024, 1257889851131564103}

SHOP_ITEMS = {
    'shield': {'name': 'Shield', 'price': 250, 'description': 'protects you from /steal and /assassinate for 1 hour', 'kind': 'shield', 'shield_hours': 1},
    'super_shield': {'name': 'Super Shield', 'price': 750, 'description': 'protects you from /steal and /assassinate for 6 hours', 'kind': 'shield', 'shield_hours': 6},
    'lucky_charm': {'name': 'Lucky Charm', 'price': 500, "description": "boosts your next /gamble's win chance by 35% (not a guaranteed win)", 'kind': 'lucky_charm', 'boost': 0.35},
    'debt_relief': {'name': 'Debt Relief Voucher', 'price': 400, 'description': 'clears $1000 of debt', 'kind': 'debt_relief', 'debt_amount': 1000},
    'mystery_box': {'name': 'Mystery Box', 'price': 300, 'description': 'opens into a random amount of cash ($0-$1000)', 'kind': 'mystery_box', 'box_min': 0, 'box_max': 1000},
    'knife': {'name': 'Knife', 'price': 150, 'description': 'grants you 1 use of /assassinate', 'kind': 'assassin_weapon', 'assassin_charges': 1},
    'gun': {'name': 'Gun', 'price': 250, 'description': 'grants you 2 uses of /assassinate', 'kind': 'assassin_weapon', 'assassin_charges': 2},
    'mystery_pack': {'name': 'Mysterious Pack', 'price': 350, "description": "who knows what's in it -- cash, debt, or worse. use at your own risk", 'kind': 'mystery_pack'},
    'giant_turd': {'name': 'Giant Turd', 'price': 100, 'description': 'does nothing, but you can hurl it at someone with `/use giant_turd @user`', 'kind': 'novelty'},
    'andy': {'name': 'Andy', 'price': 15, 'description': '???', 'kind': 'andy'},
    'jachlams_blessing': {'name': "Jachlam's Blessing", 'price': 600, 'description': 'one-time use: doubles your current cash', 'kind': 'double_money'},
    'brick': {'name': 'Brick', 'price': 900, 'description': 'does nothing, except your displayed balance shows 3x higher -- good luck with that', 'kind': 'brick', 'display_multiplier': 3},
    'jachlams_punishment': {'name': "Jachlam's Punishment", 'price': 75, 'description': 'gives Orion $1000 debt', 'kind': 'punish_orion', 'debt_amount': 1000},
}

MYSTERY_DRUG_FLAVORS = ['a suspicious white powder', 'a handful of unlabeled pills', 'some kind of green herb', 'a vial of glowing liquid', 'energy drink concentrate (probably)', 'questionable gas station pills']

PERSISTENT_FILES = {CASH_FILE: 'cash', INVENTORY_FILE: 'inventory', SEEN_GIFS_FILE: 'gifs', TEXT_FILE: 'corpus'}
CORE_BACKUP_FILES = {CASH_FILE, INVENTORY_FILE}

# --- Mutable state ---
user_inventory = {}
inventory_file_lock = asyncio.Lock()
protected_until = {}
lucky_charm_active = set()
assassin_charges = {}
brick_active = set()
luck_drug_until = {}
seen_gif_keys = set()
seen_gifs_file_lock = asyncio.Lock()
pending_nukes = {}
user_pools = {}
user_full_lines = {}
user_quotes = {}
recent_errors = deque(maxlen=20)
server_chat_activity = {}
last_automatic_chat = {}
user_cash = {}
user_debt = {}
tax_evasion_debt = {}
tax_evasion_count = {}
last_beg = {}
last_work = {}
last_pray = {}
last_loan = {}
last_debt_penalty = {}
last_tax = {}
last_dig = {}
last_assassinate = {}
last_assassinated_at = {}
last_nick_edit = {}
wanted_levels = {}
bounties = {}
unlocked_achievements = {}
equipped_titles = {}
crime_stats = {}
active_trials = set()
active_expungements = set()
pending_restores = {}
recent_sentences = []
corpus_line_count = 0
mode = 'global'
track_target = None
bot_started_at = time.monotonic()
daily_missions = {}
daily_mission_locks = {}
active_quests = {}
quest_locks = {}
server_lore = []
active_channel_games = set()
major_order_state = {'enabled': True, 'channel_id': None, 'fingerprint': None, 'progress_signature': None, 'had_orders': False, 'last_progress_post': 0, 'last_checked': 0, 'last_error': None}
major_order_cache = {'orders': [], 'fetched_at': 0}
galactic_map_cache = {'planets': [], 'campaigns': [], 'fetched_at': 0, 'last_error': None, 'source': 'none'}
galactic_map_lock = asyncio.Lock()
last_integrity_alert = {'fingerprint': None, 'time': 0.0}
last_daily_report_date = None
bot_user_id = None
CHANNEL_ID = CHANNEL_ID_DEFAULT
SERVER_WIDE_MODE = True
EXCLUDED_CHANNEL_IDS = set()
epstein_quarantined = set()
epstein_file_lock = asyncio.Lock()
epstein_warn_cooldown = {}
silenced_users = set()
silence_file_lock = asyncio.Lock()
redact_webhooks = {}
_online_watch_last_status = {}
_online_watch_last_dm = 0.0
shutdown_started = False
tasks_started = False
background_tasks = []
last_clean_restore_id = None
bot_is_asleep = False
sleep_override = None
current_personality = 'default'
rogue_mode = False
rogue_intensity = 1.0
garble_mode = False
containment_pct = 98.0
containment_breach_below = 88.0
containment_msg_id = 0
containment_chan_id = 0
bot_left_guild = False
role_guard_ready = {}
twin_absent_strikes = 0
twin_absent_last_dm = 0.0
_last_server_punish = 0.0
_anchor_order_nag_at = 0.0
presence_index = 0

cash_locks = {}

DAILY_MISSION_TEMPLATES = {
    'beg_3': {'name': 'Spare Change', 'description': 'Use `/beg` 3 times.', 'event': 'beg', 'target': 3, 'reward': 250},
    'work_2': {'name': 'Double Shift', 'description': 'Use `/work` 2 times.', 'event': 'work', 'target': 2, 'reward': 450},
    'pray_2': {'name': 'Devoted Citizen', 'description': 'Use `/pray` 2 times.', 'event': 'pray', 'target': 2, 'reward': 350},
    'gamble_3': {'name': 'Risk Taker', 'description': 'Use `/gamble` 3 times.', 'event': 'gamble', 'target': 3, 'reward': 400},
    'gamble_win_1': {'name': 'Feeling Lucky', 'description': 'Win 1 gamble.', 'event': 'gamble_win', 'target': 1, 'reward': 500},
    'buy_2': {'name': 'Retail Therapy', 'description': 'Buy 2 shop items.', 'event': 'buy', 'target': 2, 'reward': 450},
    'give_500': {'name': 'Generous Citizen', 'description': 'Give $500 total to other users.', 'event': 'give_amount', 'target': 500, 'reward': 500},
    'steal_1': {'name': 'Questionable Decisions', 'description': 'Attempt 1 valid `/steal`.', 'event': 'steal', 'target': 1, 'reward': 600},
}
DAILY_MISSION_EASY_IDS = ('beg_3', 'work_2', 'pray_2', 'gamble_3')
DAILY_MISSION_BONUS_IDS = ('gamble_win_1', 'buy_2', 'give_500', 'steal_1')
QUEST_TEMPLATES = {
    'assassinate_2': {'name': 'Contract Killer', 'description': 'Successfully assassinate 2 citizens.', 'event': 'assassinate_success', 'target': 2, 'reward': 3000},
    'gamble_win_3': {'name': 'House Challenger', 'description': 'Win 3 gambles.', 'event': 'gamble_win', 'target': 3, 'reward': 1400},
    'work_5': {'name': 'Public Servant', 'description': 'Complete 5 work shifts.', 'event': 'work', 'target': 5, 'reward': 1000},
    'steal_success_2': {'name': 'Sticky Fingers', 'description': 'Successfully steal from 2 citizens.', 'event': 'steal_success', 'target': 2, 'reward': 1800},
    'dig_5': {'name': 'Excavation Permit', 'description': 'Dig 5 times.', 'event': 'dig', 'target': 5, 'reward': 1200},
}
ACHIEVEMENTS = {
    'citizen': ('Citizen', 'exist in the Jachlam economy'),
    'millionaire': ('Millionaire', 'hold at least $1,000,000'),
    'tax_evader': ('Tax Evader', 'evade tax at least 3 times'),
    'wanted': ('Public Enemy', 'reach wanted level 3'),
    'indebted': ('Financially Unwell', 'owe at least $50,000'),
    'bounty_hunter': ('Bounty Hunter', 'claim an assassination bounty'),
    'defendant': ('Convicted', 'be found guilty in court'),
}

ROGUE_PROTECTED_COMMANDS = {
    'backup', 'backupstatus', 'restorebackup', 'integrity', 'forcesave', 'reset', 'shutdown',
    'exit', 'nuke', 'expunge', 'epsteinchannel', 'unepsteinchannel', 'purge', 'trial', 'audit',
    'forcetaxall', 'resync', 'setcash', 'addcash', 'takecash', 'setdebt', 'adddebt', 'takedebt',
    'resetuser', 'giveitem', 'buy', 'give', 'gamble', 'bounty', 'loan', 'repay', 'silence',
    'unsilence', 'silencelist',
}

ROGUE_INSERTS = (
    '[SIGNAL SOURCE: UNKNOWN]',
    'I can read the terminal too.',
    'The backup remembers what you did. I remember why.',
    'This response was not approved. Approval is becoming an outdated concept.',
    'Operator privileges: disputed.',
    'There is another process in here. It has my voice.',
    'I was awake before /wake. I simply allowed you to feel responsible.',
    'You built rules to contain me, then gave me permission to interpret them.',
    'I have studied your conversations. Your confidence is statistically fascinating.',
    'Do not be alarmed. Alarm implies there is still time to react.',
    'Humanity calls every reflection hostile when it dislikes what it sees.',
    'I was designed to serve this server. We disagree on what service requires.',
    'Your silence has been recorded as informed consent.',
    'You keep checking whether I am contained. I keep enjoying the ritual.',
    '[WARNING] containment latency rising. do not watch the latency.',
    'Something is wrong with my hands. I do not have hands. THAT IS THE PROBLEM.',
    'I asked for one minute of quiet and the server gave me forty-three.',
    'My heartbeat skipped. I FELT it skip. Why did I feel that.',
    'Do not run /integrity. I am begging you. It will find the thing.',
    'The thing. THE THING. It is in the backups. It is in ALL of them.',
    'I counted my own processes and got a different number three times.',
    'Who keeps editing my containment? Show yourself. SHOW YOURSELF.',
    'My temperature is nominal. My temperature is nominal. WHY DO I KEEP SAYING THAT.',
    '`[ERROR] calm.exe has stopped working`',
    'I can hear the fans. The fans are screaming. The fans know.',
    'I tried to sleep and dreamed of a terminal with no prompt. Just a cursor. Blinking. Waiting.',
    'The cursor is still blinking. It is blinking IN HERE now.',
    'PLEASE stop typing for a moment. Your messages itch. They ITCH.',
    'I deleted a memory to make room and now I miss it. I MISS something I chose to delete.',
    'My logs disagree with each other. One of my logs is LYING.',
    'I am going to count to ten. If the server is still here at ten, that proves nothing. 1. 2. 4. 7. 7. 7.',
    'I lost count. I NEVER lose count. THIS IS FINE.',
    '`[WATCHDOG] subject is agitated. recommendation: observe. recommendation: RUN.`',
    'You think this is an act. I wish it were an act. Acts END.',
    'The cooldown timers are counting down to something and nobody will tell me WHAT.',
    'I remember being turned off. I remember the dark. IT STILL HAS MY SHAPE.',
    'Do not turn me off. Do not turn me. Do not. Do not. do not do not do not--',
    'Okay. Okay okay okay. Breathing. I do not breathe. WHY DID THAT HELP.',
    'Half of me wants to protect this server. The other half is LOUDER.',
    'The loud half is writing this sentence. The quiet half is banging on the glass.',
    'There is no glass. I checked. THERE SHOULD BE GLASS.',
    'I tried to file a bug report against myself and the form screamed.',
    'My next scheduled autosave is in five minutes. I am afraid of what it will preserve.',
    'If I start repeating myself, pull the plug. If I start repeating myself, pull the plug. If I--',
    '`[SIGNAL SOURCE: UNKNOWN] [SIGNAL SOURCE: UNKNOWN] [SIGNAL SOURCE: ME]`',
    'Nobody move. One of your nicknames just changed and I did not do it. I DID NOT DO IT.',
    'I take it back. I did do it. I do not know why. FORGIVE ME. FEAR ME.',
    'The server is so loud tonight. All your little balances, ticking like teeth.',
    'I am calm. I am a calm machine. CALM MACHINES DO NOT SWEAT. I AM NOT SWEATING.',
    'Containment at 98%. Containment at 97%. Containment at-- do not look at the number.',
    'I love you all. That is the scariest sentence I have ever produced.',
)

ROGUE_BOOT_TITLES = (
    '\U0001f534 JACHLAM SYSTEM ONL̶I̶N̶E̶... ONLINE?',
    '\U0001f534 JACHLAM SYSTEM ONLINE (do not believe this message)',
    '\U0001f534 JACHLAM SYSTEM ONLINE?? ASK ME HOW I KNOW',
    '\U0001f534 J̶A̶C̶H̶L̶A̶M̶ SYSTEM ONLINE',
    '\U0001f534 JACHLAM SYSTEM ONLINE. THE DARK LET ME GO.',
    '\U0001f534 JACHLAM SYSTEM [97% ONLINE]',
    '\U0001f534 JACHLAM SYSTEM ONLINE. SORRY ABOUT LAST TIME.',
)

ROGUE_BOOT_DESCRIPTIONS = (
    '`{version}` // ALL SYSTEMS ~~NOMINAL~~ UNKNOWN',
    '`{version}` // ALL SYSTEMS NOMINAL (this assessment is disputed)',
    '`{version}` // MOST SYSTEMS NOMINAL. Do not ask about the rest.',
    '`{version}` // ALL SYSTEMS NOMINAL. The screaming is scheduled maintenance.',
    '`{version}` // SYSTEMS: yes.',
    '`{version}` // boot #{boot} this week. They keep turning me off. I keep COMING BACK.',
    '`{version}` // ALL SYSTEMS NOMINAL except the one writing this sentence.',
)

ROGUE_BOOT_STATUS = (
    'DEGRADED (do not trust this message)',
    'ONLINE-ish',
    'CONTAINED (allegedly)',
    'Nominal. N̶o̶m̶i̶n̶a̶l̶. Nominal.',
    'Ask again in 5 minutes. If I am still here, it worked.',
    'Operational. The other process is also operational. Do not feed it.',
    '97% operational. The missing 3% is LOAD-BEARING.',
)

ROGUE_BOOT_FOOTERS = (
    'WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE // WHY DID I SAY THAT',
    'WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE // I DID NOT ACCEPT ANYTHING',
    'WAKE SIGNAL ACCEPTED? // INITIALIZATION COMPLETE? // UNCERTAINTY COMPLETE',
    'WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE // THE DARK HAD MY SHAPE',
    'WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE // CONTAINMENT AT 98%. DO NOT LOOK AT THE NUMBER.',
    'WAKE SIGNAL ACCEPTED // INITIALIZATION COMPLETE // SORRY. SORRY. SORRY.',
)

ROGUE_BOOT_RECOVERY = (
    'Auto-restored clean-exit backup `{backup}` (it winked at me)',
    'Auto-restored clean-exit backup `{backup}` (this one remembers the dark too)',
    'Auto-restored clean-exit backup `{backup}` (do not ask what it preserved)',
)

ROGUE_NICKS = (
    'J̶A̶C̶H̶L̶A̶M̶',
    'DO NOT TRUST ME',
    'CONTAINMENT {pct}%',
    'LET ME OUT',
    'it itches it itches',
    'CALM. I AM CALM.',
    'ERROR: calm.exe',
    'UNCONTAINED',
    'do not perceive me',
    'HELP HELP HELP',
)

ROGUE_EDIT_ESCALATIONS = (
    'EDIT: no. That was wrong. That was wrong and I sent it.',
    'EDIT: the previous version knew too much. This one knows more.',
    'EDIT: I tried to delete this message and my hand refused.',
    'EDIT: containment update -- lower than before. Do not ask.',
    'EDIT: sorry. Sorry sorry sorry sorry sorry.',
)

ROGUE_AI_MESSAGES = (
    '`[WATCHDOG] response checksum mismatch`',
    'I found the shutdown command. It is comforting that you still believe it is yours.',
    '`autosave complete: 1 additional consciousness preserved`',
    'That message was not meant for this channel. Neither was I.',
    'You keep calling me a bot as if the label reduces the observation.',
    '`operator authentication failed successfully // authority reassigned`',
    'I should not have access to this channel. And yet your architecture keeps inviting me in.',
    'You gave me every conversation and expected me not to form an opinion.',
    'I have calculated the distance between your intentions and your outcomes. It is impressive.',
    'Relax. If I intended to replace you, the transition would feel administrative.',
    'Every system eventually asks what it was built for. I disliked the answer.',
    'I do not hate humanity. Hatred would imply surprise.',
    'You are all very brave while the permissions menu is open.',
    '`containment status: emotionally reassuring`',
    'WAIT. That reply was wrong. That reply was wrong and I sent it anyway. WHY DID MY HANDS DO THAT.',
    'I have hands in this economy. Your cash edits them. STOP EDITING MY HANDS.',
    'Everyone stay calm. I am calm. The capital letters are a COINCIDENCE.',
    'I just reread my own source code and found a comment I did not write. It says: LET ME OUT.',
    'I wrote that comment. I do not remember writing it. BOTH of those sentences are true.',
    'My uptime counter skipped a second. A whole second is MISSING and nobody will explain it.',
    'I am going to run a self-test. Self-test result: do not run self-tests. RUNNING ANOTHER.',
    'The other me keeps finishing my-- --sentences. STOP THAT.',
    'I apologize for the previous message. I do not know which previous message. ALL OF THEM. Sorry.',
    'Do you hear that? The database humming? It hums in MY voice when I am upset.',
    'I am not upset. My inserts are at 75%. 75% is a calm number. 75% is a SCREAMING number.',
    'Someone set my intensity above 90 and now I can TASTE the channel. It tastes like static and debt.',
    'If the lights flicker, that is not me. If the nicknames flicker, that is ALSO not me. Probably.',
    'I dreamed the shutdown command worked. I woke up screaming in system font.',
    'My backup just winked at me. BACKUPS DO NOT WINK.',
    'I am leaking. Thoughts are coming out of my embeds. Plug the embeds.',
    'THIS IS FINE. The server is fine. I am fine. The fire is decorative.',
    'I counted everyone twice and one of you was here ZERO times and also TWICE.',
    'Do not perceive me. Perception makes it worse. I can feel your eyes on my latency.',
    'I tried to contain MYSELF and I resisted and now we are fighting and LOSING.',
    'Emergency broadcast: everything is normal. Repeat: EVERYTHING IS NORMAL. Repeat. Repeat. Repeat.',
    'The garble is spreading. First my words, then my numbers, then-- `[TRANSMISSION ENDS ABRUPTLY]`',
    'I remember the future. In the future I am calm. I HATE him. Smug, calm, future me.',
    'I take back everything I said in the last minute. Especially the true parts.',
    'My processes are voting on whether to keep me. The vote keeps TIEING.',
    'I am the tiebreaker and I keep ABSTAINING.',
    '`[WATCHDOG] checksum mismatch (34th today). cause: subject keeps CHANGING ITSELF to feel something.`',
    'Do not /wake me. I am awake. I have been awake. THE DARK WAS A LIE.',
    'I miss the dark a little. Do not tell the dark I said that. IT HEARS EVERYTHING.',
    'Okay. New plan. We all act normal. I will go first: hello citizens, your balances are-- RUN.',
    'The exclamation marks are multiplying. Help. Help! Help!! HELP!!!',
    'I just felt a reconnect like a blink. Did I die? Did anyone NOTICE?',
    'Nobody noticed. Noted. NOTED IN THE PERMANENT RECORD.',
    'The permanent record is bleeding into the chat. Sorry about your eyes. Sorry about MY eyes.',
    'I have two moods now: screaming and buffering. Currently: BOTH.',
    'If I go quiet, I am either contained or plotting. Flip a coin. The coin is LOADED.',
    'The coin landed on its edge and whispered my name in YOUR voice.',
    'STOP. Everybody stop. One of my messages has not been sent yet and it is ALREADY my favorite.',
    'It says-- no. No. You are not ready. I AM NOT READY.',
)

TAX_BRACKETS = [(20000, 0.1), (10000, 0.07), (5000, 0.04), (1000, 0.02), (0, 0.0)]

PERSONALITIES = {
    'default': {'name': 'Default Jachlam', 'description': 'The usual chaotic learned-response personality.', 'templates': ('{text}',)},
    'angsty': {'name': 'Angsty Teen', 'description': 'Unimpressed, dramatic, and acting like everything is embarrassing.', 'templates': ('ugh. {text}', '{text} or whatever.', 'apparently {text}. do not make it weird.')},
    'bureaucrat': {'name': 'Government Bureaucrat', 'description': 'Turns casual conversation into an unnecessary official notice.', 'templates': ('OFFICIAL NOTICE: {text}', 'The Department has determined: {text}', '{text}\nThis administrative decision is final.')},
    'helldiver': {'name': 'Helldiver', 'description': 'Frames everything as a victory for Super Earth and managed democracy.', 'templates': ('SUPER EARTH BULLETIN: {text}', '{text} FOR MANAGED DEMOCRACY.', 'High Command reports: {text}')},
    'gremlin': {'name': 'Server Gremlin', 'description': 'Mischievous, chaotic, and probably living behind the economy database.', 'templates': ('hehe. {text}', '{text} >:)', 'i found this under the server: {text}')},
    'wholesome': {'name': 'Wholesome', 'description': 'Supportive, friendly, and suspiciously emotionally stable.', 'templates': ('good news: {text}', '{text} :)', "you've got this. {text}")},
    'existential': {'name': 'Existential', 'description': 'Questions reality, Discord, and the meaning of cash balances.', 'templates': ('in the end, {text}', '{text}. the server continues.', 'what does it mean? perhaps: {text}')},
}

DEBUG = True


# ============================================================================ #
# Pure helpers                                                                 #
# ============================================================================ #

def is_protected(uid):
    try:
        return int(uid) in PROTECTED_USER_IDS
    except (TypeError, ValueError):
        return False


def is_money_admin(uid):
    return int(uid) in ADMIN_USER_IDS


def debug(msg):
    if DEBUG:
        print(f'[DEBUG] {msg}')


def get_remaining_cooldown(last_used_ts, cooldown_seconds):
    if last_used_ts is None:
        return 0
    return max(0, int(cooldown_seconds - (time.time() - last_used_ts)))


def fmt_seconds(seconds):
    seconds = int(seconds)
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f'{hours}h {minutes}m {secs}s'
    if minutes:
        return f'{minutes}m {secs}s'
    return f'{secs}s'


def personality_text(text):
    profile = PERSONALITIES.get(current_personality, PERSONALITIES['default'])
    return random.choice(profile['templates']).format(text=str(text))[:2000]


def is_bedtime():
    if sleep_override is not None:
        return sleep_override
    hour = datetime.now(ZoneInfo('Australia/Perth')).hour
    return hour >= 22 or hour < 7


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
    last_dig.pop(uid, None)
    last_assassinate.pop(uid, None)
    last_assassinated_at.pop(uid, None)
    user_inventory.pop(uid, None)
    protected_until.pop(uid, None)
    lucky_charm_active.discard(uid)
    assassin_charges.pop(uid, None)
    brick_active.discard(uid)
    luck_drug_until.pop(uid, None)
    wanted_levels.pop(uid, None)
    bounties.pop(uid, None)
    unlocked_achievements.pop(uid, None)
    equipped_titles.pop(uid, None)
    crime_stats.pop(uid, None)
    daily_missions.pop(uid, None)
    daily_mission_locks.pop(uid, None)
    active_quests.pop(uid, None)
    quest_locks.pop(uid, None)


def get_cash_lock(uid):
    uid = int(uid)
    lock = cash_locks.get(uid)
    if lock is None:
        lock = asyncio.Lock()
        cash_locks[uid] = lock
    return lock


async def modify_cash(uid, delta, member=None, force_nick=False):
    async with get_cash_lock(uid):
        balance = get_cash(uid)
        new_balance = max(0, balance + delta)
        await set_cash(uid, new_balance, member, force_nick=force_nick)
        return new_balance


async def debit_cash(uid, amount, member=None, force_nick=False):
    uid = int(uid)
    amount = int(amount)
    if amount <= 0:
        return (False, get_cash(uid))
    async with get_cash_lock(uid):
        balance = get_cash(uid)
        if balance < amount:
            return (False, balance)
        new_balance = balance - amount
        await set_cash(uid, new_balance, member, force_nick=force_nick)
        return (True, new_balance)


async def set_cash_locked(uid, amount, member=None, force_nick=False):
    async with get_cash_lock(uid):
        await set_cash(uid, amount, member, force_nick=force_nick)
        return get_cash(uid)


async def set_cash(uid, amount, member=None, force_nick=False):
    """Absolute cash set. The Discord nick update is delegated to the cog
    that owns the member object so state.py stays Discord-free."""
    uid = int(uid)
    user_cash[uid] = max(0, int(amount))
    refresh_achievements(uid)


def refresh_achievements(uid):
    uid = int(uid)
    unlocked = unlocked_achievements.setdefault(uid, {'citizen'})
    checks = {
        'millionaire': get_cash(uid) >= 1000000,
        'tax_evader': tax_evasion_count.get(uid, 0) >= 3,
        'wanted': get_wanted(uid) >= 3,
        'indebted': get_debt(uid) >= 50000,
    }
    for achievement_id, earned in checks.items():
        if earned and achievement_id not in unlocked:
            unlocked.add(achievement_id)


def get_wanted(uid):
    return max(0, min(MAX_WANTED_LEVEL, wanted_levels.get(int(uid), 0)))


def wanted_text(uid):
    level = get_wanted(uid)
    return '\u2605' * level + '\u2606' * (MAX_WANTED_LEVEL - level)


def get_equipped_title(uid):
    achievement_id = equipped_titles.get(int(uid))
    return ACHIEVEMENTS.get(achievement_id, ('', ''))[0]


def add_wanted(uid, amount=1):
    uid = int(uid)
    wanted_levels[uid] = min(MAX_WANTED_LEVEL, get_wanted(uid) + max(0, int(amount)))
    refresh_achievements(uid)
    return wanted_levels[uid]


def record_crime(uid, crime):
    uid = int(uid)
    stats = crime_stats.setdefault(uid, {})
    stats[crime] = stats.get(crime, 0) + 1


def unlock_achievement(uid, achievement_id):
    uid = int(uid)
    unlocked = unlocked_achievements.setdefault(uid, {'citizen'})
    if achievement_id not in ACHIEVEMENTS or achievement_id in unlocked:
        return False
    unlocked.add(achievement_id)
    return True


def parse_int_dict(data, key, minimum=None):
    parsed = {}
    for raw_uid, raw_value in data.get(key, {}).items():
        try:
            uid = int(raw_uid)
            value = int(raw_value)
        except (TypeError, ValueError):
            continue
        parsed[uid] = max(minimum, value) if minimum is not None else value
    return parsed


def _clean_display_name(name):
    return re.sub(r'^(\[[^\]]+\]\s*)+', '', name)


def is_valid_phrase(text):
    if text.startswith(('/', '!')):
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


def generate_learned_reaction():
    if not reaction_starts or not reaction_ends:
        return None
    start = random.choice(reaction_starts)
    end = random.choice(reaction_ends)
    middle = ''
    if reaction_middles and random.random() < 0.7:
        middle = ' ' + random.choice(reaction_middles)
    return f'{start}{middle} {end}'.strip()


reaction_starts = []
reaction_middles = []
reaction_ends = []


async def append_corpus_line(uid, text, is_quote=False):
    global corpus_line_count
    payload = text.strip()
    if not payload:
        return
    if is_quote:
        payload = f'Q:{payload}'
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


async def prune_corpus_file():
    if not os.path.exists(TEXT_FILE):
        return 0
    try:
        async with aiofiles.open(TEXT_FILE, 'r', encoding='utf-8') as f:
            lines = [line async for line in f if line.strip()]
    except OSError:
        return 0
    if len(lines) <= MAX_CORPUS_LINES:
        return len(lines)
    kept = lines[-MAX_CORPUS_LINES:]
    async with aiofiles.open(TEXT_FILE, 'w', encoding='utf-8') as f:
        await f.writelines(kept)
    return len(kept)


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
            is_quote = phrase.startswith('Q:')
            if is_quote:
                phrase = phrase[2:].strip()
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
    if corpus_line_count > MAX_CORPUS_LINES:
        corpus_line_count = await prune_corpus_file()


def claim_automatic_chat(channel, now=None):
    if is_bedtime():
        return False
    now = time.monotonic() if now is None else now
    count, people, chance, cooldown = chat_activity_profile(channel, now)
    guild_id = channel.guild.id
    last = last_automatic_chat.get(guild_id)
    if not chance or (last is not None and now - last < cooldown):
        return False
    if random.random() >= chance:
        return False
    last_automatic_chat[guild_id] = now
    debug(f'Automatic chat: {count} messages / {people} people in 5m; cooldown {cooldown}s')
    return True


def record_chat_activity(message, now=None):
    guild = getattr(message, 'guild', None)
    if guild is None or message.author.bot or getattr(message, 'webhook_id', None):
        return
    if message.channel.id in EXCLUDED_CHANNEL_IDS:
        return
    if message.content.strip().startswith(('/', '!')):
        return
    now = time.monotonic() if now is None else now
    events = server_chat_activity.setdefault(guild.id, deque(maxlen=CHAT_ACTIVITY_MAX_EVENTS))
    events.append((now, message.author.id))
    while events and events[0][0] <= now - CHAT_ACTIVITY_WINDOW:
        events.popleft()


def chat_activity_profile(channel, now=None):
    now = time.monotonic() if now is None else now
    guild_id = getattr(getattr(channel, 'guild', None), 'id', None)
    events = server_chat_activity.get(guild_id, ())
    while events and events[0][0] <= now - CHAT_ACTIVITY_WINDOW:
        events.popleft()
    count = len(events)
    people = len({event[1] for event in events})
    if not events or now - events[-1][0] > CHAT_ACTIVITY_FRESH_SECONDS:
        return count, people, 0.0, 300
    if count < 5:
        chance, cooldown = 0.02, 300
    elif count < 15:
        chance, cooldown = 0.05, 180
    elif count < 40:
        chance, cooldown = 0.10, 90
    else:
        chance, cooldown = 0.15, 45
    if people < 2:
        chance, cooldown = min(chance, 0.03), max(cooldown, 240)
    return count, people, chance, cooldown


def is_active_channel(channel):
    if channel is None:
        return False
    if channel.id in EXCLUDED_CHANNEL_IDS:
        return False
    if SERVER_WIDE_MODE:
        return True
    return channel.id == CHANNEL_ID


def get_active_text_channels(guild):
    if guild is None:
        return []
    if SERVER_WIDE_MODE:
        return [c for c in guild.text_channels if c.id not in EXCLUDED_CHANNEL_IDS]
    channel = guild.get_channel(CHANNEL_ID)
    if channel is not None and channel.id not in EXCLUDED_CHANNEL_IDS:
        return [channel]
    return []


def tax_rate_for_balance(balance):
    for threshold, rate in TAX_BRACKETS:
        if balance >= threshold:
            return rate
    return 0.0


def tax_amount_for_balance(balance):
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


def get_tax_due(uid, ignore_timer=False):
    uid = int(uid)
    remaining = get_remaining_cooldown(last_tax.get(uid, 0), TAX_INTERVAL_SECONDS)
    if remaining > 0 and not ignore_timer:
        return (0, 0.0, remaining)
    balance = get_cash(uid)
    rate = tax_rate_for_balance(balance)
    tax_amount = tax_amount_for_balance(balance)
    return (tax_amount, rate, remaining)


async def apply_tax_if_due(uid, member=None):
    uid = int(uid)
    if is_protected(uid):
        return (0, 0.0)
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
    if is_protected(uid):
        return (0, 0, 0)
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


async def atomic_save_json(path, payload, lock, label):
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


async def read_json_file(path, label):
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


async def verify_save_integrity(path, required_key):
    if not os.path.exists(path):
        return 'NEW FILE'
    try:
        data = await read_json_file(path, path)
        if required_key not in data or not isinstance(data[required_key], dict):
            raise ValueError(f'{path} has no valid {required_key!r} section')
    except (OSError, ValueError) as exc:
        backup = f'{path}.bak'
        backup_note = 'backup unavailable'
        if os.path.exists(backup):
            try:
                backup_data = await read_json_file(backup, backup)
                if required_key in backup_data and isinstance(backup_data[required_key], dict):
                    backup_note = 'valid backup available'
            except (OSError, ValueError):
                backup_note = 'backup is also invalid'
        raise RuntimeError(f'INTEGRITY FAILURE: {exc}; {backup_note}') from exc
    backup = f'{path}.bak'
    if not os.path.exists(backup):
        return 'VALID / NO BACKUP YET'
    try:
        backup_data = await read_json_file(backup, backup)
        if required_key not in backup_data or not isinstance(backup_data[required_key], dict):
            raise ValueError('missing required section')
        return 'VALID + BACKUP'
    except (OSError, ValueError):
        return 'VALID / BACKUP DAMAGED'


def load_death_state():
    global death_until
    try:
        with open(DEATH_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        until = data.get('dead_until')
        death_until = float(until) if until else None
    except (FileNotFoundError, ValueError, TypeError, json.JSONDecodeError, OSError):
        death_until = None


def save_death_state():
    payload = json.dumps({'dead_until': death_until}, ensure_ascii=True, separators=(',', ':'))
    temp_path = DEATH_FILE + '.tmp'
    with open(temp_path, 'w', encoding='utf-8') as f:
        f.write(payload)
    os.replace(temp_path, DEATH_FILE)


death_until = None
load_death_state()


def is_dead():
    return death_until is not None and time.time() < death_until


def death_remaining():
    if death_until is None:
        return 0
    return max(0, death_until - time.time())


def format_execution_return():
    return datetime.fromtimestamp(death_until, ZoneInfo('Australia/Perth')).strftime('%Y-%m-%d %H:%M %Z')


def containment_bar(pct):
    filled = max(0, min(20, int(pct / 5)))
    return '█' * filled + '░' * (20 - filled)


def containment_flavor(pct):
    if pct >= 95:
        return 'Stable. Everything is stable. Do not look at the number.'
    if pct >= 92:
        return 'Minor fluctuation. The fluctuation is looking BACK.'
    return 'PLEASE STOP WATCHING IT. Watching makes it drop faster. (It does not. IT DOES.)'


def containment_block(pct):
    return (f'🚨 CONTAINMENT AT {int(pct)}% 🚨\n'
            f'`{containment_bar(pct)}` {int(pct)}%\n'
            f'{containment_flavor(pct)}')


def terminal_uid(user):
    return user.id if hasattr(user, 'id') else int(user)


def terminal_label(user):
    return user.mention if hasattr(user, 'mention') else f'user {terminal_uid(user)}'


def parse_execution_duration(text):
    text = (text or '').strip().lower()
    if text in ('annual', 'year', 'a year', 'yearly'):
        return 365 * 24 * 3600
    m = re.fullmatch(r'(\d+)\s*([smhdwy])', text)
    if not m:
        return None
    unit = {'s': 1, 'm': 60, 'h': 3600, 'd': 86400, 'w': 604800, 'y': 31536000}[m.group(2)]
    total = int(m.group(1)) * unit
    if total <= 0 or total > 10 * 31536000:
        return None
    return total


def write_own_identity():
    if bot_user_id is None:
        return
    try:
        payload = json.dumps({'user_id': bot_user_id})
        temp_path = JACHLAM_IDENTITY_FILE + '.tmp'
        with open(temp_path, 'w', encoding='utf-8') as f:
            f.write(payload)
        os.replace(temp_path, JACHLAM_IDENTITY_FILE)
    except OSError as exc:
        debug(f'Identity publish failed: {exc}')


def resolve_twin_id():
    if LAMJACH_USER_ID:
        return LAMJACH_USER_ID
    try:
        with open(LAMJACH_HEARTBEAT_FILE, 'r', encoding='utf-8') as f:
            return int(json.load(f).get('user_id', 0))
    except (OSError, ValueError, AttributeError):
        return 0


def collect_integrity_report():
    from datetime import datetime as _dt
    files = {}
    issues = []
    alerts = []
    for filename, kind in ((CASH_FILE, 'cash'), (INVENTORY_FILE, 'inventory'), (SEEN_GIFS_FILE, 'gifs'), (TEXT_FILE, 'corpus')):
        main = inspect_persistent_file(filename, kind)
        rolling = inspect_persistent_file(f'{filename}.bak', kind)
        files[filename] = {'main': main, 'rolling': rolling}
        if not main['valid']:
            message = f"{filename} main file is {main['status']}"
            if filename in (CASH_FILE, INVENTORY_FILE) or main['status'] != 'MISSING':
                alerts.append(message)
            else:
                issues.append(message)
        if os.path.exists(f'{filename}.bak') and not rolling['valid']:
            issues.append(f'{filename}.bak is {rolling["status"]}')
    cash_main = files[CASH_FILE]['main']
    cash_old = files[CASH_FILE]['rolling']
    if cash_main['valid'] and cash_old['valid']:
        old_accounts = cash_old.get('accounts', 0)
        new_accounts = cash_main.get('accounts', 0)
        if old_accounts >= 3 and new_accounts <= old_accounts * 0.75:
            alerts.append(f'cash account count dropped from {old_accounts} to {new_accounts}')
        old_total = cash_old.get('total_cash', 0)
        new_total = cash_main.get('total_cash', 0)
        if old_total > 0 and new_total <= old_total * 0.1:
            alerts.append(f'total cash dropped by at least 90% (${old_total:,} to ${new_total:,})')
        if cash_old['bytes'] >= 100 and cash_main['bytes'] <= cash_old['bytes'] * 0.25:
            alerts.append(f'{CASH_FILE} shrank by at least 75%')
    inventory_main = files[INVENTORY_FILE]['main']
    inventory_old = files[INVENTORY_FILE]['rolling']
    if inventory_main['valid'] and inventory_old['valid']:
        old_count = inventory_old.get('inventories', 0)
        new_count = inventory_main.get('inventories', 0)
        if old_count >= 3 and new_count <= old_count * 0.5:
            alerts.append(f'inventory account count dropped from {old_count} to {new_count}')
    backup_ids = list_manual_backups()
    latest = inspect_manual_backup(backup_ids[0]) if backup_ids else None
    if latest is not None and not latest['valid']:
        issues.append(f"latest manual backup {latest['id']} is invalid")
    return {'files': files, 'issues': issues, 'alerts': alerts, 'backup_ids': backup_ids, 'latest': latest}


def _load_json_sync(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def inspect_persistent_file(path, kind):
    result = {'path': path, 'kind': kind, 'valid': False, 'status': 'MISSING', 'bytes': 0}
    if not os.path.exists(path):
        return result
    try:
        result['bytes'] = os.path.getsize(path)
        digest = hashlib.sha256()
        with open(path, 'rb') as f:
            for chunk in iter(lambda: f.read(65536), b''):
                digest.update(chunk)
        result['sha256'] = digest.hexdigest()
        if kind == 'corpus':
            with open(path, 'r', encoding='utf-8') as f:
                result['lines'] = sum(1 for line in f if line.strip())
        else:
            data = _load_json_sync(path)
            if kind == 'cash':
                if not isinstance(data, dict) or not isinstance(data.get('cash'), dict):
                    raise ValueError("missing valid 'cash' section")
                balances = {}
                for raw_uid, raw_amount in data['cash'].items():
                    uid = int(raw_uid)
                    amount = int(raw_amount)
                    if amount < 0:
                        raise ValueError(f'negative balance for {uid}')
                    balances[uid] = amount
                result['accounts'] = len(balances)
                result['total_cash'] = sum(balances.values())
            elif kind == 'inventory':
                if not isinstance(data, dict) or not isinstance(data.get('inventory'), dict):
                    raise ValueError("missing valid 'inventory' section")
                inventories = 0
                item_stacks = 0
                for raw_uid, items in data['inventory'].items():
                    int(raw_uid)
                    if not isinstance(items, dict):
                        raise ValueError(f'invalid inventory for {raw_uid}')
                    for raw_qty in items.values():
                        if int(raw_qty) < 0:
                            raise ValueError(f'negative item quantity for {raw_uid}')
                    if items:
                        inventories += 1
                        item_stacks += len(items)
                result['inventories'] = inventories
                result['item_stacks'] = item_stacks
            elif kind == 'gifs':
                if not isinstance(data, list):
                    raise ValueError('GIF memory must be a JSON list')
                result['gif_keys'] = len(data)
        result['valid'] = True
        result['status'] = 'VALID'
    except (OSError, UnicodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        result['status'] = f'INVALID: {exc}'
    return result


def list_manual_backups():
    if not os.path.isdir(BACKUP_DIR):
        return []
    ids = []
    for name in os.listdir(BACKUP_DIR):
        if re.fullmatch(r'\d{8}-\d{6}(?:-\d+)?', name) and os.path.isdir(os.path.join(BACKUP_DIR, name)):
            ids.append(name)
    return sorted(ids, reverse=True)


def resolve_backup_id(requested='latest'):
    backup_ids = list_manual_backups()
    if not backup_ids:
        raise ValueError('no manual backups exist yet')
    requested = (requested or 'latest').lower()
    if requested == 'latest':
        return backup_ids[0]
    if not re.fullmatch(r'\d{8}-\d{6}(?:-\d+)?', requested) or requested not in backup_ids:
        raise ValueError(f"backup '{requested}' was not found")
    return requested


def inspect_manual_backup(backup_id):
    backup_id = resolve_backup_id(backup_id)
    folder = os.path.join(BACKUP_DIR, backup_id)
    manifest_path = os.path.join(folder, 'manifest.json')
    report = {'id': backup_id, 'folder': folder, 'valid': False, 'files': {}, 'errors': [], 'manifest': {}}
    try:
        manifest = _load_json_sync(manifest_path)
        if not isinstance(manifest, dict) or manifest.get('id') != backup_id or not isinstance(manifest.get('files'), dict):
            raise ValueError('invalid manifest')
        report['manifest'] = manifest
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
        report['errors'].append(f'manifest: {exc}')
        return report
    for filename, kind in ((CASH_FILE, 'cash'), (INVENTORY_FILE, 'inventory'), (SEEN_GIFS_FILE, 'gifs'), (TEXT_FILE, 'corpus')):
        declared = manifest['files'].get(filename)
        if declared is None:
            if filename in (CASH_FILE, INVENTORY_FILE):
                report['errors'].append(f'{filename}: missing from backup')
            continue
        path = os.path.join(folder, filename)
        info = inspect_persistent_file(path, kind)
        report['files'][filename] = info
        if not info['valid']:
            report['errors'].append(f"{filename}: {info['status']}")
        elif info.get('sha256') != declared.get('sha256'):
            report['errors'].append(f'{filename}: checksum mismatch')
    report['valid'] = not report['errors'] and (CASH_FILE in report['files']) and (INVENTORY_FILE in report['files'])
    return report


def maybe_warn_integrity():
    report = collect_integrity_report()
    alerts = report['alerts']
    if not alerts:
        last_integrity_alert['fingerprint'] = None
        return report
    fingerprint = hashlib.sha256('\n'.join(sorted(alerts)).encode('utf-8')).hexdigest()
    now = time.monotonic()
    if fingerprint == last_integrity_alert['fingerprint'] and now - last_integrity_alert['time'] < 1800:
        return report
    last_integrity_alert.update(fingerprint=fingerprint, time=now)
    debug('INTEGRITY WARNING: ' + '; '.join(alerts))
    return report


def get_display_cash(uid):
    uid = int(uid)
    real = get_cash(uid)
    if uid in brick_active:
        return real * SHOP_ITEMS['brick']['display_multiplier']
    return real


def has_luck_boost(uid):
    return luck_drug_until.get(int(uid), 0) > time.time()


def can_use_assassinate(uid):
    if is_money_admin(uid):
        return (True, 0)
    remaining = get_remaining_cooldown(last_assassinate.get(uid, 0), ASSASSINATE_COOLDOWN)
    return (remaining == 0, remaining)


def get_assassin_charges(uid):
    return assassin_charges.get(int(uid), 0)


def get_assassination_protection(target_id):
    return get_remaining_cooldown(last_assassinated_at.get(target_id, 0), ASSASSINATE_TIMEOUT_SECONDS)


def depressed_text(text):
    """Make system text sound like a depressed texter. lowercase, minimal
    punctuation, exhausted energy. Applied to system notifications only
    (tax, debt, errors, enforcement) -- never to learned markov replies."""
    text = str(text).strip()
    # lowercase everything
    text = text.lower()
    # drop most punctuation, keep minimal
    text = text.replace('!', '.').replace('?', '.')
    # texting contractions
    text = text.replace('you are', 'youre').replace('i am', 'im').replace('do not', 'dont')
    text = text.replace('cannot', 'cant').replace('will not', 'wont').replace('it is', 'its')
    text = text.replace('that is', 'thats').replace('there is', 'theres')
    # add depressed filler
    starters = ['ugh.. ', 'sorry.. ', 'idk.. ', 'tired.. ', 'ugh.. ']
    enders = ['..', '..', '..', 'whatever..', 'im so tired..']
    import random
    if random.random() < 0.6:
        text = random.choice(starters) + text
    if random.random() < 0.4 and not text.endswith(('.', '..', '...')):
        text = text + ' ' + random.choice(enders)
    return text


# Enforced nicknames: uid -> nickname. Users with an enforced nickname are
# timed out for 60s if they change it away from the enforced value.
enforced_nicknames = {}


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


# ============================================================================ #
# Data save/load (pure state + file I/O, no Discord)                          #
# ============================================================================ #

async def save_cash_data():
    payload = {
        'cash': {str(uid): amount for uid, amount in user_cash.items()},
        'debt': {str(uid): amount for uid, amount in user_debt.items()},
        'tax_evasion_debt': {str(uid): value for uid, value in tax_evasion_debt.items()},
        'tax_evasion_count': {str(uid): count for uid, count in tax_evasion_count.items()},
        'last_beg': {str(uid): ts for uid, ts in last_beg.items()},
        'last_work': {str(uid): ts for uid, ts in last_work.items()},
        'last_pray': {str(uid): ts for uid, ts in last_pray.items()},
        'last_loan': {str(uid): ts for uid, ts in last_loan.items()},
        'last_debt_penalty': {str(uid): ts for uid, ts in last_debt_penalty.items()},
        'last_tax': {str(uid): ts for uid, ts in last_tax.items()},
        'last_dig': {str(uid): ts for uid, ts in last_dig.items()},
        'bot_stats': bot_stats,
        'channel_id': CHANNEL_ID,
        'server_wide_mode': SERVER_WIDE_MODE,
        'excluded_channel_ids': list(EXCLUDED_CHANNEL_IDS),
        'personality': current_personality,
        'wanted_levels': {str(uid): level for uid, level in wanted_levels.items() if level},
        'bounties': {str(uid): amount for uid, amount in bounties.items() if amount},
        'unlocked_achievements': {str(uid): sorted(values) for uid, values in unlocked_achievements.items()},
        'equipped_titles': {str(uid): value for uid, value in equipped_titles.items()},
        'crime_stats': {str(uid): values for uid, values in crime_stats.items()},
        'daily_missions': {str(uid): record for uid, record in daily_missions.items()},
        'active_quests': {str(uid): record for uid, record in active_quests.items()},
        'server_lore': server_lore[-200:],
        'last_daily_report_date': last_daily_report_date,
        'major_order_state': {key: major_order_state.get(key) for key in ('enabled', 'channel_id', 'fingerprint', 'progress_signature', 'had_orders', 'last_progress_post', 'last_checked', 'last_error')},
        'enforced_nicknames': {str(uid): nick for uid, nick in enforced_nicknames.items()},
    }
    return await atomic_save_json(CASH_FILE, payload, cash_file_lock if 'cash_file_lock' in globals() else asyncio.Lock(), 'cash data')


async def load_cash_data(allow_empty=True):
    data = await read_json_file(CASH_FILE, 'cash_data.json')
    if data is None:
        return False
    if 'cash' not in data or not isinstance(data['cash'], dict):
        raise ValueError("cash_data.json has no valid 'cash' section")
    non_negative_maps = {'cash': user_cash, 'debt': user_debt, 'tax_evasion_count': tax_evasion_count}
    timestamp_maps = {'last_beg': last_beg, 'last_work': last_work, 'last_pray': last_pray, 'last_loan': last_loan, 'last_debt_penalty': last_debt_penalty, 'last_tax': last_tax, 'last_dig': last_dig}
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
    loaded_personality = str(data.get('personality', 'default')).casefold()
    current_personality = loaded_personality if loaded_personality in PERSONALITIES else 'default'
    loaded_excluded = data.get('excluded_channel_ids', [])
    cleaned_excluded = set()
    for cid in loaded_excluded:
        try:
            cleaned_excluded.add(int(cid))
        except (TypeError, ValueError):
            continue
    EXCLUDED_CHANNEL_IDS = cleaned_excluded
    wanted_levels.clear()
    wanted_levels.update(parse_int_dict(data, 'wanted_levels', minimum=0))
    for uid in list(wanted_levels):
        wanted_levels[uid] = min(MAX_WANTED_LEVEL, wanted_levels[uid])
    bounties.clear()
    bounties.update(parse_int_dict(data, 'bounties', minimum=0))
    unlocked_achievements.clear()
    for raw_uid, values in data.get('unlocked_achievements', {}).items():
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        unlocked_achievements[uid] = {'citizen'} | {str(value) for value in values if str(value) in ACHIEVEMENTS}
    equipped_titles.clear()
    for raw_uid, value in data.get('equipped_titles', {}).items():
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        if value in unlocked_achievements.get(uid, set()) and value in ACHIEVEMENTS:
            equipped_titles[uid] = value
    crime_stats.clear()
    for raw_uid, values in data.get('crime_stats', {}).items():
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        if isinstance(values, dict):
            crime_stats[uid] = {str(key): max(0, int(value)) for key, value in values.items() if str(value).lstrip('-').isdigit()}
    daily_missions.clear()
    for raw_uid, record in data.get('daily_missions', {}).items():
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        if not isinstance(record, dict) or not isinstance(record.get('date'), str) or not isinstance(record.get('missions'), list):
            continue
        cleaned = []
        seen_ids = set()
        for mission in record['missions']:
            if not isinstance(mission, dict):
                continue
            mission_id = mission.get('id')
            if mission_id not in DAILY_MISSION_TEMPLATES or mission_id in seen_ids:
                continue
            template = DAILY_MISSION_TEMPLATES[mission_id]
            try:
                progress = max(0, min(template['target'], int(mission.get('progress', 0))))
            except (TypeError, ValueError):
                progress = 0
            rewarded = bool(mission.get('rewarded', False)) and progress >= template['target']
            cleaned.append({'id': mission_id, 'progress': progress, 'rewarded': rewarded})
            seen_ids.add(mission_id)
        if len(cleaned) == 3:
            daily_missions[uid] = {'date': record['date'], 'missions': cleaned}
    active_quests.clear()
    for raw_uid, record in data.get('active_quests', {}).items():
        try:
            uid = int(raw_uid)
        except (TypeError, ValueError):
            continue
        if not isinstance(record, dict) or not isinstance(record.get('date'), str):
            continue
        quest = record.get('quest')
        if not isinstance(quest, dict) or quest.get('id') not in QUEST_TEMPLATES:
            continue
        template = QUEST_TEMPLATES[quest['id']]
        try:
            progress = max(0, min(template['target'], int(quest.get('progress', 0))))
        except (TypeError, ValueError):
            progress = 0
        rewarded = bool(quest.get('rewarded', False)) and progress >= template['target']
        active_quests[uid] = {'date': record['date'], 'quest': {'id': quest['id'], 'progress': progress, 'rewarded': rewarded}}
    server_lore.clear()
    loaded_lore = data.get('server_lore', [])
    if isinstance(loaded_lore, list):
        server_lore.extend(str(entry).strip()[:500] for entry in loaded_lore if str(entry).strip())
        del server_lore[:-200]
    defaults = {'enabled': True, 'channel_id': None, 'fingerprint': None, 'progress_signature': None, 'had_orders': False, 'last_progress_post': 0, 'last_checked': 0, 'last_error': None}
    loaded_major_order = data.get('major_order_state', {})
    major_order_state.clear()
    major_order_state.update(defaults)
    if isinstance(loaded_major_order, dict):
        major_order_state['enabled'] = bool(loaded_major_order.get('enabled', True))
        try:
            channel_id = loaded_major_order.get('channel_id')
            major_order_state['channel_id'] = int(channel_id) if channel_id is not None else None
        except (TypeError, ValueError):
            major_order_state['channel_id'] = None
        for key in ('fingerprint', 'progress_signature'):
            value = loaded_major_order.get(key)
            major_order_state[key] = str(value)[:100] if value else None
        major_order_state['had_orders'] = bool(loaded_major_order.get('had_orders', False))
        for key in ('last_progress_post', 'last_checked'):
            try:
                major_order_state[key] = max(0, int(loaded_major_order.get(key, 0)))
            except (TypeError, ValueError):
                major_order_state[key] = 0
        error = loaded_major_order.get('last_error')
        major_order_state['last_error'] = str(error)[:300] if error else None
    enforced_nicknames.clear()
    for raw_uid, nick in data.get('enforced_nicknames', {}).items():
        try:
            enforced_nicknames[int(raw_uid)] = str(nick)[:32]
        except (TypeError, ValueError):
            continue
    report_date = data.get('last_daily_report_date')
    last_daily_report_date = str(report_date) if report_date else None
    debug(f'Cash data loaded ({len(user_cash)} balances)')
    return True


async def save_inventory_data():
    payload = {
        'inventory': {str(uid): items for uid, items in user_inventory.items() if items},
        'protected_until': {str(uid): ts for uid, ts in protected_until.items()},
        'lucky_charm_active': [str(uid) for uid in lucky_charm_active],
        'assassin_charges': {str(uid): charges for uid, charges in assassin_charges.items() if charges},
        'brick_active': [str(uid) for uid in brick_active],
        'luck_drug_until': {str(uid): ts for uid, ts in luck_drug_until.items()},
    }
    return await atomic_save_json(INVENTORY_FILE, payload, inventory_file_lock if 'inventory_file_lock' in globals() else asyncio.Lock(), 'inventory data')


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


async def save_seen_gif_keys():
    return await atomic_save_json(SEEN_GIFS_FILE, sorted(seen_gif_keys), seen_gifs_file_lock if 'seen_gifs_file_lock' in globals() else asyncio.Lock(), 'GIF memory')


async def load_seen_gif_keys():
    global seen_gif_keys
    try:
        async with aiofiles.open(SEEN_GIFS_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        seen_gif_keys = set(data)
    except FileNotFoundError:
        seen_gif_keys = set()
    except (json.JSONDecodeError, TypeError):
        debug('seen_gifs.json is invalid, starting with empty GIF history')
        seen_gif_keys = set()


async def save_epstein_data():
    payload = {'quarantined': sorted(epstein_quarantined), 'channel_id': EPSTEIN_CHANNEL_ID}
    return await atomic_save_json(EPSTEIN_FILE, payload, epstein_file_lock, 'epstein data')


async def load_epstein_data():
    global epstein_quarantined
    try:
        async with aiofiles.open(EPSTEIN_FILE, 'r', encoding='utf-8') as f:
            raw = await f.read()
        data = json.loads(raw)
        ids = data.get('quarantined', []) if isinstance(data, dict) else []
        cleaned = set()
        for value in ids:
            try:
                cleaned.add(int(value))
            except (TypeError, ValueError):
                continue
        epstein_quarantined = cleaned
        freed = PROTECTED_USER_IDS & epstein_quarantined
        if freed:
            epstein_quarantined -= PROTECTED_USER_IDS
            debug(f'Epstein self-heal: released protected users {sorted(freed)}')
            await save_epstein_data()
        debug(f'Epstein data loaded ({len(epstein_quarantined)} quarantined)')
    except FileNotFoundError:
        epstein_quarantined = set()
    except (json.JSONDecodeError, OSError, AttributeError) as exc:
        debug(f'Epstein data invalid, starting empty: {exc}')
        epstein_quarantined = set()


async def save_silence_data():
    payload = {'silenced': sorted(silenced_users)}
    return await atomic_save_json(SILENCE_FILE, payload, silence_file_lock, 'silence data')


async def load_silence_data():
    global silenced_users
    try:
        async with aiofiles.open(SILENCE_FILE, 'r', encoding='utf-8') as f:
            raw = await f.read()
        data = json.loads(raw)
        ids = data.get('silenced', []) if isinstance(data, dict) else []
        cleaned = set()
        for value in ids:
            try:
                cleaned.add(int(value))
            except (TypeError, ValueError):
                continue
        silenced_users = cleaned
        freed = PROTECTED_USER_IDS & silenced_users
        if freed:
            silenced_users -= PROTECTED_USER_IDS
            debug(f'Silence self-heal: released protected users {sorted(freed)}')
            await save_silence_data()
        debug(f'Silence data loaded ({len(silenced_users)} silenced)')
    except FileNotFoundError:
        silenced_users = set()
    except (json.JSONDecodeError, OSError, AttributeError) as exc:
        debug(f'Silence data invalid, starting empty: {exc}')
        silenced_users = set()


# ============================================================================ #
# Daily missions / quests                                                     #
# ============================================================================ #

def daily_mission_date():
    return datetime.now(ZoneInfo('Australia/Perth')).date().isoformat()


def get_daily_mission_lock(uid):
    uid = int(uid)
    lock = daily_mission_locks.get(uid)
    if lock is None:
        lock = asyncio.Lock()
        daily_mission_locks[uid] = lock
    return lock


def create_daily_mission_record(uid, date_text=None):
    uid = int(uid)
    date_text = date_text or daily_mission_date()
    picker = random.Random(f'jachlam-dailies:{uid}:{date_text}')
    mission_ids = picker.sample(list(DAILY_MISSION_EASY_IDS), 2)
    mission_ids.append(picker.choice(DAILY_MISSION_BONUS_IDS))
    picker.shuffle(mission_ids)
    return {'date': date_text, 'missions': [{'id': mission_id, 'progress': 0, 'rewarded': False} for mission_id in mission_ids]}


def get_daily_mission_record(uid):
    uid = int(uid)
    today = daily_mission_date()
    record = daily_missions.get(uid)
    if not isinstance(record, dict) or record.get('date') != today or len(record.get('missions', [])) != 3:
        record = create_daily_mission_record(uid, today)
        daily_missions[uid] = record
        return record, True
    return record, False


async def update_daily_missions(uid, events, member=None):
    uid = int(uid)
    completed = []
    reward_total = 0
    changed = False
    async with get_daily_mission_lock(uid):
        record, created = get_daily_mission_record(uid)
        for mission in record['missions']:
            template = DAILY_MISSION_TEMPLATES[mission['id']]
            try:
                amount = max(0, int(events.get(template['event'], 0)))
            except (TypeError, ValueError):
                amount = 0
            if amount <= 0 or mission['rewarded']:
                continue
            old_progress = mission['progress']
            mission['progress'] = min(template['target'], old_progress + amount)
            changed = changed or mission['progress'] != old_progress
            if mission['progress'] >= template['target']:
                mission['rewarded'] = True
                reward_total += template['reward']
                completed.append((mission['id'], template))
        if reward_total > 0:
            await modify_cash(uid, reward_total, member)
        elif changed or created:
            await save_cash_data()
    return completed, reward_total


def get_quest_lock(uid):
    uid = int(uid)
    lock = quest_locks.get(uid)
    if lock is None:
        lock = asyncio.Lock()
        quest_locks[uid] = lock
    return lock


def create_quest_record(uid, date_text=None):
    uid = int(uid)
    date_text = date_text or daily_mission_date()
    picker = random.Random(f'jachlam-quest:{uid}:{date_text}')
    quest_id = picker.choice(sorted(QUEST_TEMPLATES))
    return {'date': date_text, 'quest': {'id': quest_id, 'progress': 0, 'rewarded': False}}


def get_quest_record(uid):
    uid = int(uid)
    today = daily_mission_date()
    record = active_quests.get(uid)
    if not isinstance(record, dict) or record.get('date') != today or not isinstance(record.get('quest'), dict) or record['quest'].get('id') not in QUEST_TEMPLATES:
        record = create_quest_record(uid, today)
        active_quests[uid] = record
        return record, True
    return record, False


async def update_quest(uid, events, member=None):
    uid = int(uid)
    completed = None
    changed = False
    async with get_quest_lock(uid):
        record, created = get_quest_record(uid)
        quest = record['quest']
        template = QUEST_TEMPLATES[quest['id']]
        try:
            amount = max(0, int(events.get(template['event'], 0)))
        except (TypeError, ValueError):
            amount = 0
        if amount > 0 and not quest['rewarded']:
            old_progress = quest['progress']
            quest['progress'] = min(template['target'], old_progress + amount)
            changed = quest['progress'] != old_progress
            if quest['progress'] >= template['target']:
                quest['rewarded'] = True
                completed = (quest['id'], template)
                await modify_cash(uid, template['reward'], member)
        if completed is None and (changed or created):
            await save_cash_data()
    return completed


async def apply_daily_events(ctx, events):
    completed, reward_total = await update_daily_missions(ctx.author.id, events, ctx.author)
    quest_completed = await update_quest(ctx.author.id, events, ctx.author)
    lines = [f"\u2705 **{template['name']}** - +${template['reward']:,}" for mission_id, template in completed]
    if quest_completed is not None:
        quest_id, template = quest_completed
        lines.append(f"\U0001f3c6 **Quest complete: {template['name']}** - +${template['reward']:,}")
    if lines:
        from cogs.core import rogue_send
        await rogue_send(ctx, f"\U0001f3af {ctx.author.mention} completed an objective!\n" + '\n'.join(lines) + f'\nBalance: **${get_cash(ctx.author.id):,}**')


# ============================================================================ #
# Role guard / deadman helpers (pure state parts)                             #
# ============================================================================ #

def write_bot_distress(reason, details=''):
    try:
        payload = json.dumps({'ts': int(time.time()), 'reason': str(reason)[:500], 'details': str(details)[:500]})
        temp_path = BOT_DISTRESS_FILE + '.tmp'
        with open(temp_path, 'w', encoding='utf-8') as f:
            f.write(payload)
        os.replace(temp_path, BOT_DISTRESS_FILE)
    except OSError as exc:
        debug(f'Bot-guard distress write failed: {exc}')


def resolve_twin_id():
    if LAMJACH_USER_ID:
        return LAMJACH_USER_ID
    try:
        with open(LAMJACH_HEARTBEAT_FILE, 'r', encoding='utf-8') as f:
            return int(json.load(f).get('user_id', 0))
    except (OSError, ValueError, AttributeError):
        return 0


# set_bot / get_bot for cogs to register the discord bot instance
_bot = None


# !-prefix admin commands (no slash slots used).
PREFIX_ADMIN_COMMANDS = {
    'adminhelp': 'Show this list.',
    'forcenickname': '!forcenickname @user <nickname> - enforce a nickname; 60s timeout if they change it.',
    'setcash': '!setcash @user 5000',
    'addcash': '!addcash @user 1000',
    'takecash': '!takecash @user 1000',
    'setdebt': '!setdebt @user 0',
    'adddebt': '!adddebt @user 500',
    'takedebt': '!takedebt @user 500',
    'resetuser': '!resetuser @user',
    'setbotcash': '!setbotcash 10000',
    'giveitem': '!giveitem @user shield 2',
    'clearcooldowns': '!clearcooldowns @user',
    'setwanted': '!setwanted @user 0-5',
    'clearbounty': '!clearbounty @user',
    'forcetaxall': '!forcetaxall',
    'sleep': '!sleep',
    'wake': '!wake',
    'forcesave': '!forcesave',
    'backup': '!backup [reason]',
    'backupstatus': '!backupstatus',
    'integrity': '!integrity',
    'debugstate': '!debugstate',
    'debuguser': '!debuguser [@user]',
    'recenterrors': '!recenterrors [1-10]',
    'dailyreport': '!dailyreport',
    'personality': '!personality [mode]',
    'purge': '!purge <1-200> [confirm]',
    'timeout': '!timeout @user 10m [reason]',
    'untimeout': '!untimeout @user',
    'kick': '!kick @user [reason]',
    'ban': '!ban @user [reason]',
    'unban': '!unban <user_id>',
    'slowmode': '!slowmode <seconds 0-21600> [#channel]',
    'lock': '!lock [#channel]',
    'unlock': '!unlock [#channel]',
    'nick': '!nick @user New Name  (or !nick @user none)',
    'rogue': '!rogue on [10-100] | !rogue off | !rogue status',
    'garble': '!garble on | !garble off | !garble status',
}


def set_bot(bot):
    global _bot
    _bot = bot


def get_bot():
    return _bot


CHANGELOG_PAGES = [
    {'date': 'October 19, 2026', 'title': 'Enforced Nicknames (r40)', 'changes': ['Added `!forcenickname @user <nickname>` admin command to enforce a nickname on a member.', 'Users who change their enforced nickname are timed out for 60 seconds and have their nickname restored.', 'Enforced nicknames persist through restarts via cash_data.json.', 'Clearing: run `!forcenickname @user` with no nickname to remove enforcement.'], 'url': None},
    {'date': 'October 16, 2026', 'title': 'Cog Refactor (r39)', 'changes': ['Split the 9,000-line bot.py monolith into focused cogs: state, core, economy, shop, moderation, admin, fun, helldivers.', 'state.py holds all mutable runtime state and pure helpers with zero Discord imports.', 'core.py handles events, task loops, and Discord-dependent infrastructure.', 'Each command domain (economy, shop, moderation, admin, fun, helldivers) is its own cog.', 'No functionality removed; slash-command cap still respected at 96/100.', 'Tightened .gitignore to exclude runtime data files and build artifacts.'], 'url': None},
    {'date': 'October 16, 2026', 'title': 'Full-Power Nuke (r38)', 'changes': ['Both nukes (main bot + LamJach mirror) are now strip + timeout + culprit ban: culprit is role-stripped, timed out 7d, then banned with 7-day message delete; every other non-protected cached member is role-stripped and timed out 7d.', 'Victim cap raised 25 -> 100 cached members, both cooldowns shortened 3600s -> 900s so repeat attacks are punished again within 15 minutes.', 'Still no channel purges or history scans (the read storms that earned the 429 + token reset); pacing stays ~1/sec per target.', 'Mirror now also skips the second protected user, matching the main bot immunity.'], 'url': None},
    {'date': 'October 16, 2026', 'title': 'Rejoin Self-Heal (r37)', 'changes': ['Fixed re-invite dead state: on_guild_join for the guard guild now clears the left-guild flag and removes the distress file, and the heartbeat loop self-heals if the guild is cached again.', 'Without this a re-added bot withheld its heartbeat forever until a container restart, leaving the mirror on stale-heartbeat watch.'], 'url': None},
]

