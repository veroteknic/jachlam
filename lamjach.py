"""LamJach -- the mirror twin. Like the TVA's Loom, it stands beside Jachlam
and keeps the timeline intact when Jachlam itself is attacked.

Runs as its own container (lamjach) with its OWN Discord token, so it keeps
full power even when the main bot is derolled, taken offline, or killed.
It replaces deadman.py (same-token watchdogs share one identity, so a
derolled main bot means a derolled watchdog too -- LamJach has no such
weakness).

Watches:
  1. The main Jachlam bot user -- restores its baseline roles if stripped.
  2. The protected admin user -- restores Elder / unban, same as role guard.
  3. The main bot's heartbeat -- if the main process dies AND the admin was
     harmed with restore failing, it delivers the server nuke punishment.

NUKE RULE (same as everywhere): nuke if and only if a watched user was
derolled/removed AND restoring them fails. Successful restore -> no nuke.

Discovery: the main bot writes its user id to the shared volume file
`jachlam_identity` on startup, so no manual id config is needed.

Role hierarchy note (under-mode): everything restorable sits BELOW both
bots' top roles, since Discord only lets a bot manage roles below its own
top role. Jachlam holds the server-top role and auto-stacks the anchors via
API -- no human drag needed. Target order (top to bottom): JachlamTop (held
by Jachlam) > LamJachTop (held by LamJach) > Anchor-For-LamJach (held by
LamJach) > Anchor-For-Jachlam (held by Jachlam) > Elder > everyone else.
Then Jachlam can re-add literally everything (including LamJach's top), and
LamJach can re-add everything except Jachlam's single top role.

Env:
  LAMJACH_TOKEN (or /run/discord.env containing LAMJACH_TOKEN=...;
    falls back to DISCORD_TOKEN only for local testing -- NEVER share the
    main bot's token in production or the split is pointless)
  LAMJACH_GUILD_ID (default 1409844930381090868)
  LAMJACH_DATA_DIR (default /data -- the shared volume)
  LAMJACH_CHECK_SECONDS (default 60)
  LAMJACH_GRACE_SECONDS (default 600, main-heartbeat staleness = main down)
  LAMJACH_WARMUP_SECONDS (default 300, no firing right after own start)

Commands: `!lamstatus` (admin only, prefix -- this bot registers ZERO slash
commands on purpose).
"""

import asyncio
import json
import os
import sys
import time
from datetime import datetime, timezone, timedelta

import discord

GUILD_ID = int(os.getenv("LAMJACH_GUILD_ID", "1409844930381090868"))
DATA_DIR = os.getenv("LAMJACH_DATA_DIR", "/data")
MAIN_HEARTBEAT_FILE = os.path.join(DATA_DIR, "deadman_heartbeat")
OWN_HEARTBEAT_FILE = os.path.join(DATA_DIR, "lamjach_heartbeat")
PAUSE_FILE = os.path.join(DATA_DIR, "deadman_paused")
FIRED_FILE = os.path.join(DATA_DIR, "lamjach_fired")
DISTRESS_FILE = os.path.join(DATA_DIR, "bot_distress")
BASELINE_FILE = os.path.join(DATA_DIR, "lamjach_baseline")
IDENTITY_FILE = os.path.join(DATA_DIR, "jachlam_identity")
CHECK = int(os.getenv("LAMJACH_CHECK_SECONDS", "60"))
GRACE = int(os.getenv("LAMJACH_GRACE_SECONDS", "600"))
WARMUP = int(os.getenv("LAMJACH_WARMUP_SECONDS", "300"))

ADMIN_USER_ID = int(os.getenv("LAMJACH_ADMIN_ID", "1055064009457537024"))
ELDER_ROLE_ID = int(os.getenv("LAMJACH_ELDER_ID", "1409845988599795712"))
NUKE_TIMEOUT_DAYS = 7
NUKED_COOLDOWN = 900
# Full-power nuke (last resort, restore-failed only): strip + timeout every
# non-protected cached member, ban the audit-log culprit with 7-day message
# delete. Still NO channel purges / history scans -- those read storms are
# what earned the 429 + token reset. Cap + pacing keep one firing 429-safe.
NUKE_MAX_TIMEOUTS = 100
NUKE_TIMEOUT_GAP_SECONDS = 1.0
NUKE_DELETE_MESSAGE_DAYS = 7
# Mirror of the main bot's PROTECTED_USER_IDS: these users can never be
# harmed by any nuke path.
PROTECTED_USER_IDS = {1055064009457537024, 1257889851131564103}
# Instant re-poll (on_member_update) cooldown -- prevents an event storm from
# turning into an API storm.
INSTANT_POLL_COOLDOWN = 120.0
_last_instant_poll = 0.0
# Mirror presence: refresh at most every 5 min (gateway-side, but stay
# conservative after the rate-limit lesson). Local reads only -- zero API.
PRESENCE_UPDATE_SECONDS = 300
_last_presence_update = 0.0
# Restore-success DM cooldown -- a flap war must not DM-spam the admin.
RESTORED_DM_COOLDOWN = 3600
_restored_dm_at = 0.0

TOKEN = os.getenv("LAMJACH_TOKEN")
if not TOKEN:
    for path in ("/run/discord.env", ".env"):
        try:
            with open(path, encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("LAMJACH_TOKEN="):
                        TOKEN = line.split("=", 1)[1].strip().strip("'\"")
                        break
            if TOKEN:
                break
        except OSError:
            continue
if not TOKEN:
    # Local-testing fallback only. Production MUST use a separate token.
    TOKEN = os.getenv("DISCORD_TOKEN")
    if TOKEN:
        print("[lamjach] WARNING: running on the main bot token -- split is pointless like this", flush=True)
if not TOKEN:
    print("[lamjach] NO TOKEN -- set LAMJACH_TOKEN or mount /run/discord.env", flush=True)
    sys.exit(1)

intents = discord.Intents.default()
intents.members = True
intents.message_content = True
client = discord.Client(intents=intents)

JACHLAM_USER_ID = 0  # resolved from IDENTITY_FILE, refreshed every check
last_nuke = 0.0


def log(msg):
    print(f"[lamjach] {datetime.now(timezone.utc).isoformat(timespec='seconds')} {msg}", flush=True)


def refresh_identity():
    global JACHLAM_USER_ID
    try:
        with open(IDENTITY_FILE, encoding="utf-8") as f:
            JACHLAM_USER_ID = int(json.load(f).get("user_id", 0))
    except (OSError, ValueError, AttributeError):
        pass


def read_ts(path):
    try:
        with open(path, encoding="utf-8") as f:
            return int(f.read().strip())
    except (OSError, ValueError):
        return 0


def heartbeat_age():
    ts = read_ts(MAIN_HEARTBEAT_FILE)
    return float("inf") if not ts else time.time() - ts


def read_fired():
    try:
        with open(FIRED_FILE, encoding="utf-8") as f:
            return float(f.read().strip())
    except (OSError, ValueError):
        return 0.0


def write_fired():
    try:
        with open(FIRED_FILE, "w", encoding="utf-8") as f:
            f.write(str(time.time()))
    except OSError as exc:
        log(f"could not write fired marker: {exc}")


def clear_fired():
    try:
        os.remove(FIRED_FILE)
    except OSError:
        pass


def load_baseline():
    try:
        with open(BASELINE_FILE, encoding="utf-8") as f:
            data = json.load(f)
        return {int(r) for r in data.get("jachlam_roles", [])}
    except (OSError, ValueError, AttributeError, TypeError):
        return set()


def save_baseline(role_ids):
    try:
        tmp = BASELINE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(json.dumps({"jachlam_roles": sorted(role_ids)}))
        os.replace(tmp, BASELINE_FILE)
    except OSError as exc:
        log(f"baseline save failed: {exc}")


async def dm_admin(text):
    try:
        user = client.get_user(ADMIN_USER_ID)
        if user is None:
            user = await client.fetch_user(ADMIN_USER_ID)
        await user.send(text[:2000])
        return True
    except (discord.Forbidden, discord.HTTPException) as exc:
        log(f"admin DM failed: {exc}")
        return False


def announce_channel(guild):
    me = guild.me
    if guild.system_channel is not None:
        try:
            if guild.system_channel.permissions_for(me).send_messages:
                return guild.system_channel
        except Exception:
            pass
    for channel in getattr(guild, "text_channels", []):
        try:
            if channel.permissions_for(me).send_messages:
                return channel
        except Exception:
            continue
    return None


async def find_culprit(guild, target_id, role_id=None):
    """Who stripped roles from (or banned/kicked) the target, best effort."""
    try:
        async for entry in guild.audit_logs(limit=10):
            if getattr(entry.target, "id", None) != target_id:
                continue
            if entry.action == discord.AuditLogAction.member_role_update and role_id is not None:
                before = {r.id for r in (entry.before.roles if entry.before is not None else [])}
                after = {r.id for r in (entry.after.roles if entry.after is not None else [])}
                if role_id in before and role_id not in after:
                    return entry.user
            elif entry.action in (discord.AuditLogAction.ban, discord.AuditLogAction.kick):
                return entry.user
    except (discord.Forbidden, discord.HTTPException):
        pass
    return None


async def guard_member(guild, target_id, label, baseline_roles):
    """Restore baseline roles on a watched member.

    Returns (state, note) where state is 'intact' | 'restored' | 'failed' |
    'absent'. Only 'failed' may ever lead to punishment.
    """
    reason = f"LamJach mirror guard: restoring {label}"
    try:
        member = await guild.fetch_member(target_id)
    except (discord.NotFound, discord.HTTPException):
        return ("absent", f"{label} is not in the server")
    if not baseline_roles:
        current = {r.id for r in getattr(member, "roles", [])}
        current.discard(guild.default_role.id)
        if current:
            save_baseline(current)
            log(f"baseline captured for {label}: {sorted(current)}")
        return ("intact", f"{label} baseline captured")
    missing = [guild.get_role(rid) for rid in baseline_roles]
    missing = [r for r in missing if r is not None and r not in member.roles]
    if not missing:
        return ("intact", f"{label} intact")
    try:
        await member.add_roles(*missing, reason=reason)
        still = [r for r in missing if r not in (await guild.fetch_member(target_id)).roles]
        if not still:
            return ("restored", f"{label} roles restored: {', '.join(r.name for r in missing)}")
        return ("failed", f"{label} re-add incomplete, still missing: {', '.join(r.name for r in still)}")
    except (discord.Forbidden, discord.HTTPException) as exc:
        return ("failed", f"{label} re-add failed: {exc}")


async def find_admin_ban_kick(guild):
    """(action, user) for the most recent ban/kick of the admin, else (None, None)."""
    try:
        async for entry in guild.audit_logs(limit=10):
            if getattr(entry.target, "id", None) != ADMIN_USER_ID:
                continue
            if entry.action == discord.AuditLogAction.ban:
                return ("ban", entry.user)
            if entry.action == discord.AuditLogAction.kick:
                return ("kick", entry.user)
    except (discord.Forbidden, discord.HTTPException) as exc:
        log(f"ban/kick audit lookup failed: {exc}")
    return (None, None)


async def guard_admin(guild):
    """Restore the admin's Elder role / unban. Returns (state, note)."""
    reason = "LamJach mirror guard: Elder role must always be held by the protected user"
    try:
        member = await guild.fetch_member(ADMIN_USER_ID)
        present = True
    except (discord.NotFound, discord.HTTPException):
        member, present = None, False
    if not present:
        # Removed: find out how, then try to undo it. A kick cannot be
        # undone by the bot, so it counts as restore-failed (nuke path),
        # exactly like the main bot treats it -- no more silent stand-down.
        action, _ = await find_admin_ban_kick(guild)
        if action == "kick":
            return ("failed", "admin was kicked and cannot be restored by the bot")
        try:
            await guild.fetch_ban(discord.Object(id=ADMIN_USER_ID))
            still_banned = True
        except discord.NotFound:
            still_banned = False
        except (discord.Forbidden, discord.HTTPException):
            still_banned = True
        if not still_banned:
            if action == "ban":
                return ("intact", "ban audit found but admin no longer banned")
            return ("intact", "admin absent with no ban/kick audit trail; standing down")
        try:
            await guild.unban(discord.Object(id=ADMIN_USER_ID), reason=reason)
            return ("restored", "admin unbanned")
        except (discord.Forbidden, discord.HTTPException, discord.NotFound) as exc:
            return ("failed", f"admin unban failed: {exc}")
    role = guild.get_role(ELDER_ROLE_ID)
    if role is None:
        return ("failed", "the Elder role was deleted and cannot be restored")
    if role not in member.roles:
        try:
            await member.add_roles(role, reason=reason)
            return ("restored", "Elder role restored to admin")
        except (discord.Forbidden, discord.HTTPException) as exc:
            return ("failed", f"Elder re-add failed: {exc}")
    try:
        if member.timed_out_until is not None and member.timed_out_until > discord.utils.utcnow():
            await member.remove_timeout(reason=reason)
    except (discord.Forbidden, discord.HTTPException):
        pass
    return ("intact", "admin intact")


async def server_nuke(guild, note):
    """Full-power punishment (restore-failed only): no purge/history scans.

    Purges + per-channel history reads are what earned the 429/rate-limit
    (and the token reset), so those stay out. Everything else is maxed:
    the audit-log culprit is role-stripped, timed out, then banned with
    7-day message delete; every other non-protected cached member is
    role-stripped and timed out, paced ~1/sec, cap 100. Protected users,
    bots, self, the main bot and the admin are never touched.
    """
    global last_nuke
    if time.monotonic() - last_nuke < NUKED_COOLDOWN:
        log("nuke on cooldown; skipping")
        return
    last_nuke = time.monotonic()
    reason = "LamJach mirror guard: watched user harmed and restore failed"
    culprit = await find_culprit(guild, JACHLAM_USER_ID or ADMIN_USER_ID)
    culprit_text = f" caused by {culprit.mention}" if culprit is not None else ""
    # Cached members only -- zero read API calls. Skip bots/self/protected.
    # Culprit first so they can never slip outside the cap.
    me_id = client.user.id if client.user is not None else 0
    skip_ids = set(PROTECTED_USER_IDS) | {ADMIN_USER_ID, me_id, JACHLAM_USER_ID}
    targets = []
    seen = set()
    culprit_first = 0
    cm = culprit if isinstance(culprit, discord.Member) else None
    if cm is None and culprit is not None:
        try:
            cm = guild.get_member(culprit.id)
        except Exception:
            cm = None
    if cm is not None and not getattr(cm, "bot", False) and cm.id not in skip_ids:
        targets.append(cm)
        seen.add(cm.id)
        culprit_first = 1
    skipped = 0
    for m in list(getattr(guild, "members", []) or []):
        if getattr(m, "bot", False):
            continue
        if m.id in skip_ids:
            skipped += 1
            continue
        if m.id in seen:
            continue
        # Skip anyone we cannot touch (above us in hierarchy) lazily at
        # fire time; just collect candidates here.
        targets.append(m)
        seen.add(m.id)
        if len(targets) >= NUKE_MAX_TIMEOUTS:
            break
    timeouts = fails = stripped = 0
    banned = ""
    for index, target in enumerate(targets):
        try:
            removable = [r for r in getattr(target, "roles", []) if r.id != guild.default_role.id]
            if removable:
                try:
                    await target.remove_roles(*removable, reason=reason)
                    stripped += 1
                except (discord.Forbidden, discord.HTTPException) as exc:
                    log(f"strip failed for {getattr(target, 'id', '?')}: {exc}")
            await target.timeout(timedelta(days=NUKE_TIMEOUT_DAYS), reason=reason)
            timeouts += 1
        except (discord.Forbidden, discord.HTTPException) as exc:
            fails += 1
            log(f"timeout failed for {getattr(target, 'id', '?')}: {exc}")
        except Exception as exc:
            fails += 1
            log(f"timeout failed for {getattr(target, 'id', '?')}: {type(exc).__name__}: {exc}")
        # Culprit gets the maximum: ban with 7-day message delete on top.
        if index == 0 and culprit_first:
            try:
                await guild.ban(target, reason=reason, delete_message_days=NUKE_DELETE_MESSAGE_DAYS)
                banned = f" culprit {target.mention} banned ({NUKE_DELETE_MESSAGE_DAYS}d message delete)."
            except (discord.Forbidden, discord.HTTPException, discord.NotFound) as exc:
                log(f"culprit ban failed for {getattr(target, 'id', '?')}: {exc}")
            except Exception as exc:
                log(f"culprit ban failed for {getattr(target, 'id', '?')}: {type(exc).__name__}: {exc}")
        await asyncio.sleep(NUKE_TIMEOUT_GAP_SECONDS)
    text = (f"\U0001f4a5 LAMJACH FIRED: {note}{culprit_text}. "
            f"{timeouts} timed out, {stripped} role-stripped ({fails} failed, {skipped} protected skipped, cap {NUKE_MAX_TIMEOUTS}, culprit-first {culprit_first}).{banned} "
            f"No channel purges (timeout/strip/ban mode).")
    dest = announce_channel(guild)
    if dest is not None:
        try:
            await dest.send(text)
        except (discord.Forbidden, discord.HTTPException):
            pass
    await dm_admin(text)
    log(f"nuke done (strip/timeout/ban): timeouts={timeouts} stripped={stripped} fails={fails} banned={bool(banned)}")


async def handle_violation(guild, label, state, note):
    """Alert always; nuke if and only if restore failed."""
    global _restored_dm_at
    log(f"verdict for {label}: {state} -- {note}")
    if state in ("intact", "restored"):
        if state == "restored":
            # Cooldown-gated: a flap war (strip every minute) must not DM-spam
            # the admin; hourly is plenty for good news.
            now = time.monotonic()
            if now - _restored_dm_at >= RESTORED_DM_COOLDOWN:
                _restored_dm_at = now
                await dm_admin(f"\U0001f6e1\ufe0f LamJach mirror guard: {note}. No punishment -- restore succeeded.")
            else:
                log("restored DM on cooldown; skipping")
        return
    if state == "absent":
        await dm_admin(f"\u26a0\ufe0f LamJach mirror guard: {note}. Standing down (no ban/kick trail).")
        return
    await dm_admin(f"\U0001f6a8 LamJach mirror guard: {note}. Restore FAILED -- punishing the server now.")
    await server_nuke(guild, note)


async def poll_guild():
    guild = client.get_guild(GUILD_ID)
    if guild is None:
        try:
            guild = await client.fetch_guild(GUILD_ID)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
            log(f"guild fetch failed: {exc}")
            return
    refresh_identity()
    # 1. Main bot roles.
    if JACHLAM_USER_ID:
        state, note = await guard_member(guild, JACHLAM_USER_ID, "main bot Jachlam", load_baseline())
        await handle_violation(guild, "main bot", state, note)
    else:
        log("main bot identity unknown yet (waiting for jachlam_identity)")
    # 2. Admin Elder.
    state, note = await guard_admin(guild)
    await handle_violation(guild, "admin", state, note)
    # 3. Main heartbeat: main process dead?
    age = heartbeat_age()
    paused = os.path.exists(PAUSE_FILE)
    if age <= GRACE:
        if read_fired():
            clear_fired()
            log("main heartbeat fresh again; fired marker cleared")
        # Distress file: main bot reported its own derole while still alive.
        try:
            with open(DISTRESS_FILE, encoding="utf-8") as f:
                distress = json.load(f)
            dts = float(distress.get("ts", 0))
        except (OSError, ValueError, AttributeError):
            dts = 0.0
        if dts > read_fired() and dts > 0:
            log(f"distress file present ({distress.get('reason')}) -- re-checking now")
            write_fired()
        return
    if paused:
        return
    log(f"MAIN HEARTBEAT STALE ({age:.0f}s) -- main bot may be down; checking watched users")
    if not read_fired():
        await dm_admin(f"\u26a0\ufe0f LamJach mirror: main Jachlam heartbeat stale ({int(age)}s). Checking the admin and standing by.")
    write_fired()


@client.event
async def on_ready():
    log(f"mirror online as {client.user} (guard guild {GUILD_ID})")
    try:
        await update_mirror_presence(force=True)
    except Exception as exc:
        log(f"initial presence failed: {type(exc).__name__}: {exc}")
    client.loop.create_task(watch_loop())


async def update_mirror_presence(force=False):
    """Show the guard state in the mirror's own status. Local reads only
    (baseline file, heartbeat file, cached guild) -- zero Discord API calls,
    so it can never contribute to a rate limit."""
    global _last_presence_update
    now = time.monotonic()
    if not force and now - _last_presence_update < PRESENCE_UPDATE_SECONDS:
        return
    _last_presence_update = now
    try:
        baseline = load_baseline()
        raw_age = time.time() - read_ts(MAIN_HEARTBEAT_FILE)
        hb = f"{int(raw_age)}s" if 0 <= raw_age < 1000000000 else "never"
        guild = client.get_guild(GUILD_ID)
        elder_ok = guild is not None and guild.get_role(ELDER_ROLE_ID) is not None
        if raw_age <= GRACE:
            name = f"\U0001fa9e guarding Jachlam ({len(baseline)} roles) | hb {hb}"
        else:
            name = f"\u26a0\ufe0f main silent {hb} | guarding admin"
        if not elder_ok:
            name = f"\U0001f6a8 Elder gone | {name}"
        await client.change_presence(
            activity=discord.Activity(type=discord.ActivityType.watching, name=name[:128]))
        log(f"presence: {name[:128]}")
    except Exception as exc:
        log(f"presence failed: {type(exc).__name__}: {exc}")


async def watch_loop():
    await asyncio.sleep(WARMUP)
    while True:
        try:
            # Own proof-of-life so the main bot can watch the mirror back.
            try:
                with open(OWN_HEARTBEAT_FILE, "w", encoding="utf-8") as f:
                    f.write(str(int(time.time())))
            except OSError as exc:
                log(f"own heartbeat failed: {exc}")
            await poll_guild()
            await update_mirror_presence()
        except Exception as exc:
            log(f"watch loop error: {type(exc).__name__}: {exc}")
        await asyncio.sleep(CHECK)


@client.event
async def on_member_update(before, after):
    global _last_instant_poll
    if getattr(after, "guild", None) is None or after.guild.id != GUILD_ID:
        return
    refresh_identity()
    watched = {ADMIN_USER_ID}
    if JACHLAM_USER_ID:
        watched.add(JACHLAM_USER_ID)
    if after.id not in watched:
        return
    before_ids = {r.id for r in before.roles}
    after_ids = {r.id for r in after.roles}
    if before_ids - after_ids:
        log(f"instant detect: roles removed from {after.id}: {sorted(before_ids - after_ids)}")
        now = time.monotonic()
        if now - _last_instant_poll < INSTANT_POLL_COOLDOWN:
            log("instant poll on cooldown; skipping (periodic loop will cover)")
            return
        _last_instant_poll = now
        try:
            await poll_guild()
        except Exception as exc:
            log(f"instant poll failed: {exc}")


@client.event
async def on_message(message):
    if message.author.bot or not (message.content or "").strip().startswith("!"):
        return
    parts = message.content.strip()[1:].split(None, 1)
    if not parts or parts[0].lower() != "lamstatus":
        return
    perms = getattr(message.author, "guild_permissions", None)
    if message.author.id != ADMIN_USER_ID and not bool(perms and perms.administrator):
        try:
            await message.channel.send("not allowed")
        except (discord.Forbidden, discord.HTTPException):
            pass
        return
    guild = client.get_guild(GUILD_ID)
    baseline = sorted(load_baseline())
    try:
        age = time.time() - read_ts(MAIN_HEARTBEAT_FILE)
        hb = f"{int(age)}s ago" if age >= 0 else "never"
    except (OSError, ValueError):
        hb = "never"
    mm = guild.get_member(JACHLAM_USER_ID) if guild and JACHLAM_USER_ID else None
    main_text = "unknown" if mm is None else f"{len(mm.roles)} roles"
    try:
        await message.channel.send(
            f"\U0001fa9e LamJach mirror: main Jachlam **{main_text}** | baseline **{len(baseline)}** roles | "
            f"main heartbeat **{hb}** | Elder exists **{guild.get_role(ELDER_ROLE_ID) is not None if guild else '?'}**")
    except (discord.Forbidden, discord.HTTPException):
        pass


# Guarded entry: fatal startup errors (missing portal intents, dead token)
# sleep an hour before exiting instead of hot-looping. Docker restarts the
# container, but an hourly nap caps reconnects at ~24/day -- Discord reset
# our token once over a 1000-connects crash loop; never again.
while True:
    try:
        client.run(TOKEN)
    except discord.PrivilegedIntentsRequired:
        log("FATAL: privileged intents not enabled in the portal -- sleeping 1h")
    except discord.LoginFailure:
        log("FATAL: token rejected -- sleeping 1h (check LAMJACH_TOKEN)")
    except Exception as exc:
        log(f"exited: {type(exc).__name__}: {exc} -- sleeping 1h")
    try:
        time.sleep(3600)
    except KeyboardInterrupt:
        break
    # Re-read a rotated token without needing a redeploy. Checks env first,
    # then the mounted secret file (/run/discord.env) and local .env, so a
    # Discord-forced token reset only needs the file updated + container restart
    # (or this hourly wake) to recover.
    fresh = os.getenv("LAMJACH_TOKEN")
    if not fresh:
        for path in ("/run/discord.env", ".env"):
            try:
                with open(path, encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line.startswith("LAMJACH_TOKEN="):
                            fresh = line.split("=", 1)[1].strip().strip("'\"")
                            break
                if fresh:
                    break
            except OSError:
                continue
    if fresh and fresh != TOKEN:
        TOKEN = fresh
        log("picked up a new LAMJACH_TOKEN")
