import asyncio
import json
import os
from pathlib import Path

import discord
from discord.ext import commands


# ============================================================
# JACHLAM - VOICE CASTING
# ============================================================
#
# Put this file in the same directory as your bot.
#
# Create:
#     characters.txt
#
# with one character per line, for example:
#
#     Yuji Itadori
#     Megumi Fushiguro
#     Nobara Kugisaki
#     Satoru Gojo
#
# Blank lines and lines beginning with # are ignored.
#
# Then load it from your main bot with:
#
#     await bot.load_extension("jachlam_voicecast_download")
#
# Commands:
#     /voicecast             open the signup for the current episode
#     /voicecast_reset       close the episode and reopen it, archiving the cast
#     /voicecast_progression show who played what across every episode
#     /voicecast_fullreset   erase all casting history and start over
#
# Signup state is saved to voicecast_data.json, and each finished episode is
# archived to voicecast_episode<N>.json. Saves are atomic and mirrored to
# voicecast_data.json.bak, and the signup board is re-attached on startup so it
# stays clickable after a restart. A save file that cannot be read never reopens
# signup, because that would silently discard every existing claim.
#
# One claim per member: a member who already holds a role cannot take a second.
#
# NOTE: save_data() writes with os.replace(), which fails with EBUSY when the
# target is an individually bind-mounted file. If you run this in Docker, mount
# the whole /app directory (or a named volume) rather than mounting each data
# file separately, or every save here will fail silently.
# ============================================================


CHARACTER_FILE = Path("characters.txt")
DATA_FILE = Path("voicecast_data.json")
PAGE_SIZE = 25

_save_lock = None


def get_save_lock():
    """Serialize disk writes so two claims cannot interleave the backup copy."""
    global _save_lock

    if _save_lock is None:
        _save_lock = asyncio.Lock()

    return _save_lock


async def save_data_async():
    """Save without blocking the event loop; the claim itself stays atomic."""
    async with get_save_lock():
        await asyncio.to_thread(save_data)


voicecast_state = {
    "started": False,
    "assignments": {},  # character -> Discord user ID
    "message_id": None,  # the live signup board, so it can be restored
    "channel_id": None,
    "damaged": False,  # save data existed but was unreadable
    "episode": 1,  # bumped by /voicecast reset for the next dub episode
    "page": 0,  # so a restart does not yank members back to page 1
}


def load_characters():
    if not CHARACTER_FILE.exists():
        raise FileNotFoundError(CHARACTER_FILE)

    characters = []

    for raw_line in CHARACTER_FILE.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()

        if not line or line.startswith("#"):
            continue

        if line not in characters:
            characters.append(line)

    return characters


def apply_data(data):
    """Copy validated save data into the live state."""
    voicecast_state["started"] = bool(data.get("started", False))

    assignments = {}

    for character, user_id in data.get("assignments", {}).items():
        try:
            assignments[str(character)] = int(user_id)
        except (TypeError, ValueError):
            print(f"[VOICECAST] Dropping unusable claim for {character!r}.")

    voicecast_state["assignments"] = assignments
    voicecast_state["message_id"] = data.get("message_id")
    voicecast_state["channel_id"] = data.get("channel_id")

    try:
        voicecast_state["episode"] = max(1, int(data.get("episode", 1)))
    except (TypeError, ValueError):
        voicecast_state["episode"] = 1

    try:
        voicecast_state["page"] = max(0, int(data.get("page", 0)))
    except (TypeError, ValueError):
        voicecast_state["page"] = 0


def load_data():
    """Restore the cast from the main save file, falling back to the backup.

    A damaged file must never quietly reset `started`, or the one-time
    signup reopens and every claim is lost.
    """
    found_any = False

    for path in (DATA_FILE, Path(f"{DATA_FILE}.bak")):
        if not path.exists():
            continue

        found_any = True

        try:
            raw = path.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"[VOICECAST] Could not read {path}: {exc}")
            continue

        if not raw.strip():
            print(f"[VOICECAST] {path} is blank.")
            continue

        try:
            data = json.loads(raw)
        except json.JSONDecodeError as exc:
            print(f"[VOICECAST] {path} contains invalid JSON: {exc}")
            continue

        if not isinstance(data, dict):
            print(f"[VOICECAST] {path} must contain a JSON object.")
            continue

        if "started" not in data:
            print(f"[VOICECAST] {path} has no 'started' key; treating it as damaged.")
            continue

        try:
            apply_data(data)
        except (TypeError, ValueError) as exc:
            print(f"[VOICECAST] {path} is unusable: {exc}")
            continue

        if path != DATA_FILE:
            print("[VOICECAST] Recovered the cast from the backup file.")
            save_data()

        return True

    if found_any:
        voicecast_state["damaged"] = True
        print("[VOICECAST] No readable save data; signup stays locked.")
        return False

    return False


def is_readable(text):
    """True when the text holds a save object, not just parseable JSON."""
    try:
        return isinstance(json.loads(text), dict)
    except json.JSONDecodeError:
        return False


def save_data():
    """Write atomically so a forced stop cannot truncate the cast.

    The backup is refreshed only after the new main file is in place, and
    only from a main file that actually parsed. Copying the old main over
    the backup first would destroy the one good copy whenever the replace
    fails, which is exactly when the backup is needed.
    """
    payload = json.dumps(
        {
            "started": voicecast_state["started"],
            "assignments": voicecast_state["assignments"],
            "message_id": voicecast_state["message_id"],
            "channel_id": voicecast_state["channel_id"],
            "episode": voicecast_state["episode"],
            "page": voicecast_state["page"],
        },
        indent=4,
    )

    temp_path = f"{DATA_FILE}.tmp"
    previous_text = None

    try:
        Path(temp_path).write_text(payload, encoding="utf-8")

        if DATA_FILE.exists():
            try:
                previous_text = DATA_FILE.read_text(encoding="utf-8")
            except OSError as exc:
                print(f"[VOICECAST] Could not read the previous save: {exc}")

        os.replace(temp_path, DATA_FILE)
    except OSError as exc:
        print(f"[VOICECAST] Failed to save voicecast data: {exc}")
        return False

    if previous_text is not None and is_readable(previous_text):
        try:
            Path(f"{DATA_FILE}.bak").write_text(previous_text, encoding="utf-8")
        except OSError as exc:
            print(f"[VOICECAST] Could not refresh the backup file: {exc}")

    return True


def get_user_id(character):
    return voicecast_state["assignments"].get(character)


def get_claim(user_id):
    """Return the character this user already holds, if any."""
    for character, owner in voicecast_state["assignments"].items():
        if owner == user_id:
            return character

    return None


def make_embed(bot, characters, page=0):
    total_pages = max(1, (len(characters) + PAGE_SIZE - 1) // PAGE_SIZE)

    start = page * PAGE_SIZE
    current = characters[start:start + PAGE_SIZE]

    embed = discord.Embed(
        title=f"🎙️ Voice Casting — Episode {voicecast_state['episode']}",
        description=(
            "Pick a character from the dropdown to claim them.\n"
            "One role each, and each character can only be claimed once."
        ),
        color=discord.Color.blurple(),
    )

    lines = []

    for character in current:
        user_id = get_user_id(character)

        if user_id is None:
            status = "🟢 Available"
        else:
            user = bot.get_user(user_id)
            name = user.mention if user else f"<@{user_id}>"
            status = f"🔴 {name}"

        lines.append(f"**{character}** — {status}")

    embed.add_field(
        name=f"Characters ({start + 1}-{min(start + PAGE_SIZE, len(characters))})",
        value="\n".join(lines) if lines else "No characters.",
        inline=False,
    )

    embed.set_footer(text=f"Page {page + 1}/{total_pages}")

    return embed


class CharacterSelect(discord.ui.Select):
    def __init__(self, cog, characters, page):
        self.cog = cog
        self.characters = characters
        self.page = page

        start = page * PAGE_SIZE
        current = characters[start:start + PAGE_SIZE]

        options = [
            discord.SelectOption(
                label=character[:100],
                value=character,
                description="Available" if get_user_id(character) is None else "Already claimed",
            )
            for character in current
        ]

        super().__init__(
            placeholder="Choose a character...",
            options=options,
            custom_id=f"voicecast_select_{page}",
        )

    async def callback(self, interaction: discord.Interaction):
        character = self.values[0]

        existing_user_id = get_user_id(character)

        if existing_user_id is not None:
            if existing_user_id == interaction.user.id:
                await interaction.response.send_message(
                    f"You already claimed **{character}**.",
                    ephemeral=True,
                )
            else:
                await interaction.response.send_message(
                    f"**{character}** has already been claimed.",
                    ephemeral=True,
                )
            return

        already_holding = get_claim(interaction.user.id)

        if already_holding is not None:
            await interaction.response.send_message(
                f"You already claimed **{already_holding}**. "
                "One role each, so the rest of the cast can be filled.",
                ephemeral=True,
            )
            return

        voicecast_state["assignments"][character] = interaction.user.id
        await save_data_async()

        await interaction.response.edit_message(
            embed=make_embed(self.cog.bot, self.characters, self.page),
            view=VoiceCastView(self.cog, self.characters, self.page),
        )

        await interaction.followup.send(
            f"Claimed **{character}** for you.",
            ephemeral=True,
        )


class VoiceCastView(discord.ui.View):
    def __init__(self, cog, characters, page=0):
        super().__init__(timeout=None)

        self.cog = cog
        self.characters = characters
        self.page = page

        total_pages = max(1, (len(characters) + PAGE_SIZE - 1) // PAGE_SIZE)

        self.add_item(CharacterSelect(cog, characters, page))

        if page > 0:
            previous = discord.ui.Button(
                label="Previous",
                style=discord.ButtonStyle.secondary,
                custom_id=f"voicecast_prev_{page}",
            )

            async def previous_callback(interaction):
                target = max(0, self.page - 1)
                voicecast_state["page"] = target
                await save_data_async()

                await interaction.response.edit_message(
                    embed=make_embed(
                        self.cog.bot,
                        self.characters,
                        target,
                    ),
                    view=VoiceCastView(
                        self.cog,
                        self.characters,
                        target,
                    ),
                )

            previous.callback = previous_callback
            self.add_item(previous)

        if page < total_pages - 1:
            next_button = discord.ui.Button(
                label="Next",
                style=discord.ButtonStyle.secondary,
                custom_id=f"voicecast_next_{page}",
            )

            async def next_callback(interaction):
                target = self.page + 1
                voicecast_state["page"] = target
                await save_data_async()

                await interaction.response.edit_message(
                    embed=make_embed(
                        self.cog.bot,
                        self.characters,
                        target,
                    ),
                    view=VoiceCastView(
                        self.cog,
                        self.characters,
                        target,
                    ),
                )

            next_button.callback = next_callback
            self.add_item(next_button)


class VoiceCastCog(commands.Cog):
    def __init__(self, bot):
        self.bot = bot
        load_data()

    async def cog_load(self):
        await self.restore_board()

    async def restore_board(self):
        """Re-attach the live view after a restart.

        The dropdown custom IDs are derived from the page number, so the
        rebuilt view binds to the same message the members already have.
        """
        message_id = voicecast_state["message_id"]
        channel_id = voicecast_state["channel_id"]

        if not message_id or not channel_id:
            return

        channel = self.bot.get_channel(channel_id)

        if channel is None:
            try:
                channel = await self.bot.fetch_channel(channel_id)
            except (discord.NotFound, discord.HTTPException) as exc:
                print(f"[VOICECAST] Could not reach the signup board: {exc}")
                return

        try:
            message = await channel.fetch_message(message_id)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
            print(f"[VOICECAST] Could not restore the signup board: {exc}")
            return

        try:
            characters = load_characters()
        except FileNotFoundError:
            characters = list(voicecast_state["assignments"])

        total_pages = max(1, (len(characters) + PAGE_SIZE - 1) // PAGE_SIZE)
        page = min(voicecast_state["page"], total_pages - 1)

        try:
            await message.edit(
                embed=make_embed(self.bot, characters, page),
                view=VoiceCastView(self, characters, page),
            )
            print(
                f"[VOICECAST] Signup board restored "
                f"({len(voicecast_state['assignments'])} claimed, page {page + 1}/{total_pages})."
            )
        except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
            print(f"[VOICECAST] Could not re-attach the signup board: {exc}")

    @commands.hybrid_command(
        name="voicecast",
        description="Start the one-time voice casting signup.",
    )
    @commands.has_permissions(administrator=True)
    async def voicecast(self, ctx: commands.Context):
        if voicecast_state["damaged"]:
            await ctx.send(
                f"❌ `{DATA_FILE}` exists but could not be read, and neither could its "
                "backup. The signup stays locked so existing claims aren't lost. "
                "Restore the file from a backup, then restart the bot."
            )
            return

        if voicecast_state["started"]:
            await ctx.send(
                "❌ The voice casting signup has already been started. "
                "This command is one-time only."
            )
            return

        try:
            characters = load_characters()
        except FileNotFoundError:
            await ctx.send(
                f"❌ `{CHARACTER_FILE}` does not exist. "
                "Create it with one character per line."
            )
            return

        if not characters:
            await ctx.send(
                f"❌ `{CHARACTER_FILE}` contains no characters."
            )
            return

        voicecast_state["started"] = True
        voicecast_state["page"] = 0
        await save_data_async()

        view = VoiceCastView(self, characters)

        message = await ctx.send(
            embed=make_embed(self.bot, characters),
            view=view,
        )

        voicecast_state["message_id"] = message.id
        voicecast_state["channel_id"] = ctx.channel.id
        await save_data_async()

    @commands.hybrid_command(
        name="voicecast_reset",
        description="Close the current casting and reopen it for the next episode.",
    )
    @commands.has_permissions(administrator=True)
    async def voicecast_reset(self, ctx: commands.Context):
        if voicecast_state["damaged"]:
            await ctx.send(
                f"❌ `{DATA_FILE}` could not be read. Restore it from a backup "
                "before resetting."
            )
            return

        if not voicecast_state["started"] and not voicecast_state["assignments"]:
            await ctx.send("Nothing to reset; the signup was never started.")
            return

        finished = voicecast_state["episode"]
        cast = dict(voicecast_state["assignments"])

        if cast:
            archive = Path(f"voicecast_episode{finished}.json")
            try:
                archive.write_text(
                    json.dumps(
                        {
                            "episode": finished,
                            "assignments": cast,
                        },
                        indent=4,
                    ),
                    encoding="utf-8",
                )
            except OSError as exc:
                await ctx.send(f"❌ Could not archive episode {finished}: {exc}")
                return

        await self.close_board()

        voicecast_state["assignments"] = {}
        voicecast_state["started"] = False
        voicecast_state["message_id"] = None
        voicecast_state["channel_id"] = None
        voicecast_state["episode"] = finished + 1
        voicecast_state["page"] = 0
        await save_data_async()

        summary = (
            f"\n{len(cast)} role(s) archived to `{archive.name}`."
            if cast else "\nNothing had been claimed."
        )

        await ctx.send(
            f"✅ Episode {finished} closed.{summary}\n"
            f"Run `/voicecast` again to open episode {finished + 1}."
        )

    async def close_board(self):
        """Disable the old board so nobody can claim on a closed signup."""
        message_id = voicecast_state["message_id"]
        channel_id = voicecast_state["channel_id"]

        if not message_id or not channel_id:
            return

        try:
            channel = self.bot.get_channel(channel_id) or await self.bot.fetch_channel(channel_id)
            message = await channel.fetch_message(message_id)

            closed = discord.Embed(
                title=f"🎙️ Voice Casting — Episode {voicecast_state['episode']}",
                description=(
                    "This casting is closed.\n"
                    f"{len(voicecast_state['assignments'])} role(s) were cast."
                ),
                color=discord.Color.dark_grey(),
            )

            await message.edit(embed=closed, view=None)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException) as exc:
            print(f"[VOICECAST] Could not close the signup board: {exc}")

    @voicecast.error
    async def voicecast_error(self, ctx, error):
        if isinstance(error, commands.MissingPermissions):
            await ctx.send(
                "❌ You need administrator permissions to start voice casting."
            )
        else:
            raise error

    @voicecast_reset.error
    async def voicecast_reset_error(self, ctx, error):
        if isinstance(error, commands.MissingPermissions):
            await ctx.send(
                "❌ You need administrator permissions to reset voice casting."
            )
        else:
            raise error

    @commands.hybrid_command(
        name="voicecast_fullreset",
        description="Erase every episode, archive included, and start over at episode 1.",
    )
    @commands.has_permissions(administrator=True)
    async def voicecast_fullreset(self, ctx: commands.Context, confirmation: str = ""):
        if confirmation.lower() != "confirm":
            await ctx.send(
                "⚠️ This erases the **entire** casting history: the current signup, "
                "every archived episode file, and the episode counter. It cannot be "
                "undone.\nRun `/voicecast_fullreset confirm` to do it."
            )
            return

        archives = sorted(Path(".").glob("voicecast_episode*.json"))
        removed = []

        for archive in archives:
            try:
                archive.unlink()
                removed.append(archive.name)
            except OSError as exc:
                await ctx.send(f"❌ Could not delete `{archive.name}`: {exc}")
                return

        await self.close_board()

        voicecast_state["assignments"] = {}
        voicecast_state["started"] = False
        voicecast_state["message_id"] = None
        voicecast_state["channel_id"] = None
        voicecast_state["episode"] = 1
        voicecast_state["page"] = 0
        await save_data_async()

        await ctx.send(
            f"🗑️ Casting history erased. "
            f"Deleted {len(removed)} archive(s){': ' + ', '.join(removed) if removed else ''}.\n"
            "The counter is back at episode 1; run `/voicecast` to start fresh."
        )

    @commands.hybrid_command(
        name="voicecast_progression",
        description="Show who has played which character across every episode.",
    )
    async def voicecast_progression(self, ctx: commands.Context):
        history = {}

        for archive in Path(".").glob("voicecast_episode*.json"):
            try:
                episode = int(archive.stem.removeprefix("voicecast_episode"))
            except ValueError:
                continue

            try:
                data = json.loads(archive.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue

            if isinstance(data, dict) and isinstance(data.get("assignments"), dict):
                history[episode] = data["assignments"]

        if voicecast_state["assignments"]:
            history[voicecast_state["episode"]] = dict(voicecast_state["assignments"])

        if not history:
            await ctx.send("No casting history yet. Run `/voicecast` to open episode 1.")
            return

        embed = discord.Embed(
            title="🎬 Casting Progression",
            description=f"{len(history)} episode(s) on record.",
            color=discord.Color.blurple(),
        )

        roles = {}

        for episode in sorted(history):
            cast = history[episode]
            status = " (open)" if episode == voicecast_state["episode"] else ""
            lines = []

            for character, user_id in sorted(cast.items()):
                user = self.bot.get_user(user_id)
                mention = user.mention if user else f"<@{user_id}>"
                lines.append(f"**{character}** — {mention}")
                roles.setdefault(user_id, []).append((episode, character))

            embed.add_field(
                name=f"Episode {episode}{status} — {len(cast)} role(s)",
                value="\n".join(lines) if lines else "No roles claimed.",
                inline=False,
            )

        recurring = [
            (user_id, entries)
            for user_id, entries in roles.items()
            if len(entries) > 1
        ]

        if recurring:
            summary = []

            for user_id, entries in sorted(recurring, key=lambda item: -len(item[1])):
                user = self.bot.get_user(user_id)
                mention = user.mention if user else f"<@{user_id}>"
                played = ", ".join(
                    f"{character} (ep{episode})" for episode, character in sorted(entries)
                )
                summary.append(f"{mention} — {played}")

            embed.add_field(
                name="Recurring cast",
                value="\n".join(summary)[:1024],
                inline=False,
            )

        await ctx.send(embed=embed)

    @voicecast_fullreset.error
    async def voicecast_fullreset_error(self, ctx, error):
        if isinstance(error, commands.MissingPermissions):
            await ctx.send(
                "❌ You need administrator permissions to reset voice casting."
            )
        else:
            raise error


async def setup(bot):
    await bot.add_cog(VoiceCastCog(bot))
