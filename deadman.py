"""Dead man's switch for Jachlam. Runs as its own container
(jachlam-deadman) from the same image and watches the main bot's heartbeat
file in the shared data volume.

If the heartbeat goes stale for longer than GRACE_SECONDS (default 600) --
i.e. the main bot was killed or wedged -- and no maintenance pause file is
present, this connects with the bot token, restores the admin user's Elder
role / timeout state, then delivers the server-wide nuke punishment to
Oopy Goopy, and disconnects.

Maintenance: `touch /app/deadman_paused` inside the main container before
planned downtime, `rm` it after. deploy.sh does this automatically.

Env:
  DISCORD_TOKEN (or /run/discord.env containing DISCORD_TOKEN=...)
  DEADMAN_GUILD_ID (default 1409844930381090868)
  DEADMAN_DATA_DIR (default /data)
  DEADMAN_GRACE_SECONDS (default 600)
  DEADMAN_CHECK_SECONDS (default 60)
  DEADMAN_WARMUP_SECONDS (default 300, no firing right after own start)
"""

import asyncio
import os
import sys
import time
from datetime import datetime, timezone, timedelta

import discord

GUILD_ID = int(os.getenv("DEADMAN_GUILD_ID", "1409844930381090868"))
DATA_DIR = os.getenv("DEADMAN_DATA_DIR", "/data")
HEARTBEAT_FILE = os.path.join(DATA_DIR, "deadman_heartbeat")
PAUSE_FILE = os.path.join(DATA_DIR, "deadman_paused")
FIRED_FILE = os.path.join(DATA_DIR, "deadman_fired")
GRACE = int(os.getenv("DEADMAN_GRACE_SECONDS", "600"))
CHECK = int(os.getenv("DEADMAN_CHECK_SECONDS", "60"))
WARMUP = int(os.getenv("DEADMAN_WARMUP_SECONDS", "300"))

ADMIN_USER_ID = 1055064009457537024
ELDER_ROLE_ID = 1409845988599795712
NUKE_TIMEOUT_DAYS = 7

TOKEN = os.getenv("DISCORD_TOKEN")
if not TOKEN:
    try:
        with open("/run/discord.env", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line.startswith("DISCORD_TOKEN="):
                    TOKEN = line.split("=", 1)[1].strip().strip("'\"")
                    break
    except OSError:
        pass
if not TOKEN:
    print("[deadman] NO TOKEN -- set DISCORD_TOKEN or mount /run/discord.env", flush=True)
    sys.exit(1)


def log(msg):
    print(f"[deadman] {datetime.now(timezone.utc).isoformat(timespec='seconds')} {msg}", flush=True)


def heartbeat_age():
    try:
        with open(HEARTBEAT_FILE, encoding="utf-8") as f:
            return time.time() - int(f.read().strip())
    except (OSError, ValueError):
        return float("inf")


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


async def restore_or_need_nuke(guild):
    """Returns (nuke_needed, note). Restores the admin user when possible;
    nuke is needed if and only if the admin was derolled/removed AND the
    restore failed."""
    reason = "Dead man's switch: main bot is down and admin role was unguarded"
    try:
        member = await guild.fetch_member(ADMIN_USER_ID)
        present = True
    except (discord.NotFound, discord.HTTPException):
        member, present = None, False
    if not present:
        action = None
        try:
            async for entry in guild.audit_logs(limit=10):
                if getattr(entry.target, "id", None) != ADMIN_USER_ID:
                    continue
                if entry.action == discord.AuditLogAction.ban:
                    action = "ban"
                    break
                if entry.action == discord.AuditLogAction.kick:
                    action = "kick"
                    break
        except (discord.Forbidden, discord.HTTPException):
            pass
        if action == "ban":
            try:
                await guild.fetch_ban(discord.Object(id=ADMIN_USER_ID))
            except discord.NotFound:
                return (False, "ban audit found but user no longer banned")
            except (discord.Forbidden, discord.HTTPException):
                pass
            try:
                await guild.unban(discord.Object(id=ADMIN_USER_ID), reason=reason)
                return (False, "admin unbanned")
            except (discord.Forbidden, discord.HTTPException, discord.NotFound):
                return (True, "The protected user was banned and the unban failed.")
        if action == "kick":
            return (True, "The protected user was kicked and cannot be restored by the bot.")
        return (False, "admin absent with no ban/kick audit trail; standing down")
    role = guild.get_role(ELDER_ROLE_ID)
    if role is None:
        return (True, "The protected Elder role was deleted and cannot be restored.")
    if role not in member.roles:
        try:
            await member.add_roles(role, reason=reason)
            return (False, "Elder role restored")
        except (discord.Forbidden, discord.HTTPException):
            return (True, "The protected Elder role was removed and re-adding it failed.")
    try:
        if member.timed_out_until is not None and member.timed_out_until > discord.utils.utcnow():
            await member.remove_timeout(reason=reason)
    except (discord.Forbidden, discord.HTTPException):
        pass
    return (False, "admin intact")


async def server_nuke(guild, client):
    me = guild.me
    reason = "Dead man's switch: admin restore failed"
    purged = channels = timeouts = timeout_fails = 0
    for channel in list(getattr(guild, "text_channels", [])):
        try:
            perms = channel.permissions_for(me)
        except Exception:
            continue
        if not (perms.send_messages and perms.manage_messages and perms.read_message_history):
            continue
        members = {}
        try:
            async for msg in channel.history(limit=100):
                author = msg.author
                if getattr(author, "bot", False) or author.id == client.user.id:
                    continue
                if author.id == ADMIN_USER_ID:
                    continue
                if isinstance(author, discord.Member):
                    members[author.id] = author
        except (discord.Forbidden, discord.HTTPException):
            continue
        try:
            deleted = await channel.purge(limit=200, reason=reason)
            purged += len(deleted)
            channels += 1
        except (discord.Forbidden, discord.HTTPException):
            pass
        for target in members.values():
            try:
                await target.timeout(timedelta(days=NUKE_TIMEOUT_DAYS), reason=reason)
                timeouts += 1
            except (discord.Forbidden, discord.HTTPException):
                timeout_fails += 1
    announcement = (f"\U0001f4a5 dead man's switch fired: the main bot went dark, the admin user was harmed, "
                    f"and restoring them failed. {purged} messages purged across {channels} channels, "
                    f"{timeouts} timed out ({timeout_fails} failed).")
    dest = guild.system_channel
    if dest is None:
        for channel in guild.text_channels:
            try:
                if channel.permissions_for(me).send_messages:
                    dest = channel
                    break
            except Exception:
                continue
    if dest is not None:
        try:
            await dest.send(announcement)
        except (discord.Forbidden, discord.HTTPException):
            pass
    log(f"done: purged={purged} channels={channels} timeouts={timeouts} fails={timeout_fails}")


async def fire():
    """Connect, inspect the admin user, restore if harmed, nuke if and only
    if the restore failed. Disconnect afterwards."""
    intents = discord.Intents.default()
    intents.members = True
    client = discord.Client(intents=intents)

    @client.event
    async def on_ready():
        try:
            log(f"connected as {client.user}; inspecting admin state")
            guild = client.get_guild(GUILD_ID)
            if guild is None:
                try:
                    guild = await client.fetch_guild(GUILD_ID)
                except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
                    log(f"guild fetch failed: {exc}")
                    return
            nuke_needed, note = await restore_or_need_nuke(guild)
            log(f"verdict: {note} | nuke_needed={nuke_needed}")
            if nuke_needed:
                await server_nuke(guild, client)
        finally:
            await client.close()

    await client.start(TOKEN)


async def main():
    log(f"watching heartbeat (grace={GRACE}s check={CHECK}s warmup={WARMUP}s)")
    started = time.monotonic()
    while True:
        await asyncio.sleep(CHECK)
        age = heartbeat_age()
        paused = os.path.exists(PAUSE_FILE)
        if age <= GRACE:
            if read_fired():
                clear_fired()
                log("heartbeat fresh again; fired marker cleared")
            continue
        if paused:
            continue
        if time.monotonic() - started < WARMUP:
            log(f"heartbeat stale ({age:.0f}s) but still in warmup; waiting")
            continue
        try:
            fired_at = read_fired()
        except Exception:
            fired_at = 0.0
        try:
            hb_mtime = os.path.getmtime(HEARTBEAT_FILE)
        except OSError:
            hb_mtime = 0.0
        if fired_at > hb_mtime and fired_at > 0:
            continue  # already punished for this outage
        log(f"HEARTBEAT STALE ({age:.0f}s) -- firing dead man's switch")
        try:
            await fire()
        except Exception as exc:
            log(f"fire failed: {type(exc).__name__}: {exc}")
            await asyncio.sleep(CHECK)
            continue
        write_fired()


asyncio.run(main())
