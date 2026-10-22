"""Jachlam Fun Cog — markov replies, quotes, guessing games, lore, and fun commands.

All functions are module-level so they can be imported by other cogs without
circular imports. Discord-dependent helpers are imported lazily inside each
function.
"""

import random
import time
import discord
from discord.ext import commands

from cogs import state as S


class Fun(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @commands.hybrid_command(name='force', description='Force Jachlam to send one learned phrase immediately.')
    async def force(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        await send_phrase_reply(ctx.channel, automatic=False)

    @commands.hybrid_command(name='global', description="Return Jachlam's language model to the global learned corpus.")
    async def global_cmd(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        S.mode = 'global'
        S.track_target = None
        from cogs.core import rogue_send
        await rogue_send(ctx, 'language model returned to the global learned corpus.')

    @commands.hybrid_command(name='imitate', description="Learn/respond from one member's phrases for five minutes.")
    async def imitate(self, ctx, user: discord.Member):
        if not S.is_active_channel(ctx.channel):
            return
        S.mode = 'track'
        S.track_target = user.id
        from cogs.core import rogue_send
        await rogue_send(ctx, f'now learning from {user.mention} for five minutes.')

    @commands.hybrid_command(name='quote', description='Send a random saved quote, optionally from one user.')
    async def quote(self, ctx, user: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        uid = user.id if user else None
        pool = S.user_quotes.get(uid, []) if uid else []
        if not pool:
            if uid:
                from cogs.core import rogue_send
                await rogue_send(ctx, f'{user.mention} has no saved quotes.')
            else:
                all_quotes = [q for quotes in S.user_quotes.values() for q in quotes]
                if not all_quotes:
                    from cogs.core import rogue_send
                    await rogue_send(ctx, 'no quotes saved yet.')
                    return
                pool = all_quotes
        from cogs.core import rogue_send
        await rogue_send(ctx, f'> {random.choice(pool)}')

    @commands.hybrid_command(name='quoteadd', description='Save your own text as a quote.')
    async def quoteadd(self, ctx, *, text: str):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        S.user_quotes.setdefault(uid, []).append(text.strip())
        await S.append_corpus_line(uid, text.strip(), is_quote=True)
        await S.save_cash_data()
        from cogs.core import rogue_send
        await rogue_send(ctx, 'quote saved.')

    @commands.hybrid_command(name='quotereply', description='Save a Discord message as a quote using its message link or ID.')
    async def quotereply(self, ctx, message_ref: str):
        if not S.is_active_channel(ctx.channel):
            return
        import re
        match = re.search(r'\d{15,25}', message_ref)
        if not match:
            from cogs.core import rogue_send
            await rogue_send(ctx, 'could not find a message ID in that link.')
            return
        msg_id = int(match.group(0))
        try:
            message = await ctx.channel.fetch_message(msg_id)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            from cogs.core import rogue_send
            await rogue_send(ctx, 'could not fetch that message.')
            return
        uid = message.author.id
        S.user_quotes.setdefault(uid, []).append(message.content)
        await S.append_corpus_line(uid, message.content, is_quote=True)
        await S.save_cash_data()
        from cogs.core import rogue_send
        await rogue_send(ctx, f'quote saved from {message.author.mention}.')

    @commands.hybrid_command(name='quotes', description='Browse saved quotes in pages.')
    async def quotes(self, ctx, user: discord.Member = None, page: int = 1):
        if not S.is_active_channel(ctx.channel):
            return
        uid = user.id if user else None
        pool = S.user_quotes.get(uid, []) if uid else []
        if not pool:
            if uid:
                from cogs.core import rogue_send
                await rogue_send(ctx, f'{user.mention} has no saved quotes.')
            else:
                from cogs.core import rogue_send
                await rogue_send(ctx, 'no quotes saved yet.')
                return
        start = (page - 1) * S.QUOTES_PAGE_SIZE
        chunk = pool[start:start + S.QUOTES_PAGE_SIZE]
        if not chunk:
            from cogs.core import rogue_send
            await rogue_send(ctx, 'page out of range.')
            return
        lines = [f'> {q}' for q in chunk]
        embed = discord.Embed(
            title=f'quotes for {user.display_name if user else "everyone"} (page {page})',
            description='\n'.join(lines),
            color=discord.Color.purple(),
        )
        from cogs.core import rogue_send
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='rick', description='Post the full built-in rickroll message.')
    async def rick(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        from cogs.core import rogue_send
        await rogue_send(ctx, 'Never gonna give you up, never gonna let you down, never gonna run around and desert you. Never gonna make you cry, never gonna say goodbye, never gonna tell a lie and hurt you.')

    @commands.hybrid_command(name='yesorno', description='Make Jachlam answer yes or no for a named subject.')
    async def yesorno(self, ctx, name: str, *, question: str = ''):
        if not S.is_active_channel(ctx.channel):
            return
        answer = random.choice(['yes', 'no', 'maybe', 'ask again later'])
        from cogs.core import rogue_send
        await rogue_send(ctx, f'**{name}**: {answer}. {question}'.strip())

    @commands.hybrid_command(name='image', description='Fetch a random meme image.')
    async def image(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        from cogs.core import rogue_send
        await rogue_send(ctx, 'https://http.cat/200.jpg')

    @commands.hybrid_command(name='dig', description='Dig every five minutes for cash, items, weapon charges, debt, or absolutely nothing.')
    async def dig(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        uid = ctx.author.id
        remaining = S.get_remaining_cooldown(S.last_dig.get(uid, 0), S.LAST_DIG_COOLDOWN)
        if remaining > 0:
            from cogs.core import rogue_send
            await rogue_send(ctx, f'The hole needs time to settle. Dig again in **{S.fmt_seconds(remaining)}**.')
            return
        S.last_dig[uid] = int(time.time())
        await S.save_cash_data()
        outcome = random.choices(('nothing', 'cash', 'shield', 'gun', 'box', 'debt'), weights=(38, 30, 12, 7, 8, 5), k=1)[0]
        if outcome == 'cash':
            amount = random.randint(50, 350)
            from cogs.core import modify_cash
            await modify_cash(uid, amount, ctx.author)
            result = f'You found **${amount:,}** in damp government currency.'
        elif outcome == 'shield':
            S.add_item(uid, 'shield', 1)
            await S.save_inventory_data()
            result = 'You found **1x Shield**. It was buried for legal reasons.'
        elif outcome == 'gun':
            S.assassin_charges[uid] = S.get_assassin_charges(uid) + 2
            await S.save_inventory_data()
            result = 'You found a **Gun**, granting **2 assassination charges**.'
        elif outcome == 'box':
            S.add_item(uid, 'mystery_box', 1)
            await S.save_inventory_data()
            result = 'You found **1x Mystery Box**. This is probably fine.'
        elif outcome == 'debt':
            amount = random.randint(100, 500)
            S.user_debt[uid] = S.get_debt(uid) + amount
            await S.save_cash_data()
            result = f'You uncovered an old invoice and gained **${amount:,} debt**.'
        else:
            result = random.choice(('You found absolutely nothing.', 'You found a smaller hole.', 'You found a note saying STOP DIGGING.', 'You found dirt. Historic dirt.'))
        from cogs.core import rogue_send, apply_daily_events
        await rogue_send(ctx, f'\u26cf\ufe0f {ctx.author.mention} digs...\n{result}')
        await apply_daily_events(ctx, {'dig': 1})

    async def run_guessing_game(self, ctx, prompt, answers, reward, reveal):
        channel_id = ctx.channel.id
        if channel_id in S.active_channel_games:
            from cogs.core import rogue_send
            await rogue_send(ctx, 'A guessing game is already running in this channel.')
            return
        S.active_channel_games.add(channel_id)
        try:
            from cogs.core import rogue_send
            await rogue_send(ctx, prompt)
        except Exception:
            S.active_channel_games.discard(channel_id)
            raise
        deadline = time.monotonic() + 30
        try:
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    from cogs.core import rogue_send
                    await rogue_send(ctx, f'\u23f0 Time. The answer was **{reveal}**.')
                    return
                try:
                    message = await self.bot.wait_for('message', timeout=remaining, check=lambda candidate: candidate.channel.id == channel_id and not candidate.author.bot)
                except asyncio.TimeoutError:
                    from cogs.core import rogue_send
                    await rogue_send(ctx, f'\u23f0 Time. The answer was **{reveal}**.')
                    return
                guess = message.content.casefold().strip()
                if guess in answers:
                    from cogs.core import modify_cash
                    await modify_cash(message.author.id, reward, message.author)
                    from cogs.core import rogue_send
                    await rogue_send(ctx, f'\u2705 {message.author.mention} got it: **{reveal}** and won **${reward:,}**.')
                    return
        finally:
            S.active_channel_games.discard(channel_id)

    @commands.hybrid_command(name='emoji', description='Start a 30-second channel emoji guessing game; the first correct answer wins $250.')
    async def emoji_game(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        puzzles = [
            ('\U0001f525', {'fire', 'flame', '\U0001f525'}, 'I am hot, bright, and terrible near curtains.'),
            ('\U0001f47b', {'ghost', '\U0001f47b'}, 'I haunt places and say boo.'),
            ('\U0001f4b8', {'money with wings', 'flying money', '\U0001f4b8'}, 'I describe your cash immediately after gambling.'),
            ('\U0001f6e1\ufe0f', {'shield', '\U0001f6e1', '\U0001f6e1\ufe0f'}, 'I protect you from theft and assassination.'),
            ('\U0001f52b', {'gun', 'water pistol', '\U0001f52b'}, 'In Jachlam I grant two assassination charges.'),
        ]
        emoji, answers, hint = random.choice(puzzles)
        words = [answer for answer in answers if answer.isascii()]
        reveal = f'{emoji} ({words[0] if words else "emoji"})'
        prompt = f'\U0001f9e9 **EMOJI GUESS - $250**\nHint: {hint}\nFirst correct answer in 30 seconds wins.'
        await self.run_guessing_game(ctx, prompt, {answer.casefold() for answer in answers}, 250, reveal)

    @commands.hybrid_command(name='anagram', description='Start a 30-second word unscrambling game; the first correct answer wins $300.')
    async def anagram(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        words = ('assassinate', 'government', 'inventory', 'conspiracy', 'economy', 'jumpscare', 'citizen', 'bounty', 'shield', 'backup')
        word = random.choice(words)
        letters = list(word)
        scrambled = word
        while scrambled == word:
            random.shuffle(letters)
            scrambled = ''.join(letters)
        await self.run_guessing_game(ctx, f'\U0001f524 **ANAGRAM - $300**\nUnscramble: **{scrambled.upper()}**\nFirst correct answer in 30 seconds wins.', {word}, 300, word)

    @commands.hybrid_command(name='wouldyourather', description='Post a random Jachlam would-you-rather question.')
    async def would_you_rather(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        questions = [
            'have five wanted stars forever, or owe Jachlam $100,000 forever?',
            'win every gamble but receive no money, or lose every gamble but look extremely cool?',
            'fight one Andy-sized Jachlam, or one hundred Jachlam-sized Andys?',
            'know every server secret, or have everyone believe every conspiracy you post?',
            'get a free gun with no charges, or a free shield that expires in ten seconds?',
            'be audited once per day, or appear in every newspaper headline?',
        ]
        from cogs.core import rogue_send
        await rogue_send(ctx, f'\U0001f914 **WOULD YOU RATHER...**\n{random.choice(questions)}')

    @commands.hybrid_command(name='prediction', description='Make an unreliable prediction about selected or recent members.')
    async def prediction(self, ctx, user_one: discord.Member = None, user_two: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        members = await self.story_members(ctx, 2, (user_one, user_two))
        first = self.story_name(members[0] if members else None)
        second = self.story_name(members[1] if len(members) > 1 else None, 'Jachlam')
        predictions = [
            f'{first} will discover a second inventory hidden inside the first one.',
            f'{first} will blame {second} for an economic event that has not happened yet.',
            f'{first} and {second} will accidentally start a newspaper war before Friday.',
            f'{first} will dig up exactly one useful object and immediately sell it.',
            f'{second} will save {first} using a backup nobody remembers creating.',
        ]
        embed = discord.Embed(title='\U0001f52e DEFINITELY UNRELIABLE PREDICTION', description=random.choice(predictions), color=discord.Color.magenta())
        embed.set_footer(text='Entertainment only. The future has not signed this statement.')
        from cogs.core import rogue_send
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='conspiracy', description='Create an explicitly fictional conspiracy about selected or recent members.')
    async def conspiracy(self, ctx, user_one: discord.Member = None, user_two: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        members = await self.story_members(ctx, 2, (user_one, user_two))
        first = self.story_name(members[0] if members else None)
        second = self.story_name(members[1] if len(members) > 1 else None, 'Jachlam')
        theories = [
            f'{first} and {second} are secretly replacing every deleted message with government coupons.',
            f'{first} is three shields in a trench coat, and {second} has known since Tuesday.',
            f'{first} invented server tax solely to fund {second} moving the general channel two pixels left.',
            f'{first} and {second} have been swapping usernames to confuse the audit department.',
            f'{first} controls the coin flip results; {second} controls the dramatic sound effects.',
        ]
        embed = discord.Embed(title='\U0001f6f8 COMPLETELY FICTIONAL CONSPIRACY', description=random.choice(theories), color=discord.Color.dark_teal())
        embed.set_footer(text='Absurd server fiction, not a factual allegation.')
        from cogs.core import rogue_send
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='news', description='Publish a live server newspaper with economy, crime, bounty, activity, and satire.')
    async def news(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        citizen_ids = [member.id for member in ctx.guild.members if not member.bot] if ctx.guild is not None else list(S.user_cash)
        cash_ids = [uid for uid in citizen_ids if uid in S.user_cash]
        wanted_ids = [uid for uid in citizen_ids if S.get_wanted(uid) > 0]
        bounty_ids = [uid for uid in citizen_ids if S.bounties.get(uid, 0) > 0]
        richest_id = max(cash_ids, key=S.user_cash.get) if cash_ids else None
        wanted_id = max(wanted_ids, key=S.get_wanted) if wanted_ids else None
        bounty_id = max(bounty_ids, key=S.bounties.get) if bounty_ids else None
        recent = []
        async for message in ctx.channel.history(limit=50):
            if not message.author.bot and message.id != ctx.message.id:
                recent.append(message)
        headlines = [
            'Local economy survives another five minutes without intervention.',
            'Department confirms the hole behind the shop is not an approved bank.',
            'Experts warn that buying more guns may result in owning more assassination charges.',
            'Server residents demand answers; Jachlam supplies a leaderboard instead.',
        ]
        embed = discord.Embed(title='\U0001f4f0 THE DAILY JACHLAM', description=f'**{datetime.now(S.AWST).strftime("%d %B %Y")}**\n\n{random.choice(headlines)}', color=discord.Color.dark_gold())
        embed.add_field(name='Economy', value=f'Richest: **{S.display_user(richest_id)}** (${S.user_cash.get(richest_id, 0):,})' if richest_id else 'No accounts loaded.', inline=False)
        embed.add_field(name='Crime Desk', value=f'Most wanted: **{S.display_user(wanted_id)}** ({S.wanted_text(wanted_id)})' if wanted_id else 'No wanted citizens.', inline=True)
        embed.add_field(name='Bounty Board', value=f'**{S.display_user(bounty_id)}** (${S.bounties.get(bounty_id, 0):,})' if bounty_id else 'No active bounties.', inline=True)
        embed.add_field(name='Channel Activity', value=f'**{len(recent)}** recent messages from **{len({message.author.id for message in recent})}** citizens.', inline=False)
        if S.server_lore:
            embed.add_field(name='From the Archives', value=random.choice(S.server_lore)[:500], inline=False)
        embed.set_footer(text='Some headlines are satire. Financial numbers are live.')
        from cogs.core import rogue_send
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='rate', description='Give the same text a deterministic rating out of 100 and 10.')
    async def rate(self, ctx, *, thing: str):
        if not S.is_active_channel(ctx.channel):
            return
        seed = sum(ord(c) for c in thing.casefold())
        rng = random.Random(seed)
        score100 = rng.randint(0, 100)
        score10 = rng.randint(0, 10)
        from cogs.core import rogue_send
        await rogue_send(ctx, f'I rate "{thing}" **{score100}/100** ({score10}/10).')

    @commands.hybrid_command(name='coinflip', description='Flip a fair virtual coin.')
    async def coinflip(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        from cogs.core import rogue_send
        await rogue_send(ctx, f'\U0001fa99 **{random.choice(("HEADS", "TAILS"))}**')

    @commands.hybrid_command(name='roast', description='Send a random light server roast.')
    async def roast(self, ctx, user: discord.Member = None):
        if not S.is_active_channel(ctx.channel):
            return
        target = user or ctx.author
        roasts = [
            f'{target.mention} is the reason the warning labels exist.',
            f'{target.mention} brings everyone down to their level.',
            f'{target.mention} could screw up a wet dream.',
        ]
        from cogs.core import rogue_send
        await rogue_send(ctx, random.choice(roasts))

    @commands.hybrid_command(name='jumpscare', description='Fetch a random safe creepy image.')
    async def jumpscare(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        from cogs.core import rogue_send
        await rogue_send(ctx, 'https://http.cat/418.jpg')

    @commands.hybrid_command(name='lore', description='Generate absurd server lore or retrieve an admin-approved canon event.')
    async def lore(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        if S.server_lore:
            from cogs.core import rogue_send
            await rogue_send(ctx, f'*{random.choice(S.server_lore)}*')
        else:
            from cogs.core import rogue_send
            await rogue_send(ctx, 'The archives are empty. Run `/loreadd` to seed them.')

    @commands.hybrid_command(name='loreadd', description='Add a persistent official event to the server lore archive.')
    async def loreadd(self, ctx, *, event: str):
        if not S.is_active_channel(ctx.channel):
            return
        if not S.is_money_admin(ctx.author.id):
            permissions = getattr(ctx.author, 'guild_permissions', None)
            if not (permissions and permissions.administrator):
                from cogs.core import rogue_send
                await rogue_send(ctx, 'not allowed')
                return
        S.server_lore.append(event.strip()[:500])
        if len(S.server_lore) > 200:
            S.server_lore = S.server_lore[-200:]
        await S.save_cash_data()
        from cogs.core import rogue_send
        await rogue_send(ctx, 'lore added to the archives.')

    @commands.hybrid_command(name='blame', description='File a joke accusation.')
    async def blame(self, ctx, user: discord.Member, *, reason: str = 'existing'):
        if not S.is_active_channel(ctx.channel):
            return
        from cogs.core import rogue_send
        await rogue_send(ctx, f'{ctx.author.mention} blames {user.mention} for {reason}.')
        if S.is_money_admin(ctx.author.id) or (getattr(ctx.author, 'guild_permissions', None) and ctx.author.guild_permissions.administrator):
            S.add_wanted(user.id, 1)
            await rogue_send(ctx, f'{user.mention} gained a wanted star for being blamed by an administrator.')

    @commands.hybrid_command(name='summarize', description='Extract activity and the latest snippets from recent human messages.')
    async def summarize(self, ctx, count: int = 50):
        if not S.is_active_channel(ctx.channel):
            return
        count = max(10, min(100, count))
        messages = []
        async for message in ctx.channel.history(limit=count):
            if not message.author.bot and message.content.strip():
                messages.append(f'{message.author.display_name}: {message.content[:100]}')
        if not messages:
            from cogs.core import rogue_send
            await rogue_send(ctx, 'nothing to summarize.')
            return
        messages.reverse()
        from cogs.core import rogue_send
        await rogue_send(ctx, 'recent activity:\n' + '\n'.join(messages[-20:]))

    # -------- Helpers --------

    async def get_recent_human_members(self, channel, limit=25):
        recent = []
        async for message in channel.history(limit=limit):
            if not message.author.bot and message.id is not None:
                recent.append(message.author)
        seen = set()
        unique = []
        for member in recent:
            if member.id not in seen:
                seen.add(member.id)
                unique.append(member)
        return unique

    async def story_members(self, ctx, count, users):
        found = [u for u in users if u is not None]
        while len(found) < count:
            async for message in ctx.channel.history(limit=50):
                if not message.author.bot and message.author.id not in {u.id for u in found}:
                    found.append(message.author)
                    if len(found) >= count:
                        break
        return found[:count]

    def story_name(self, member, fallback='Jachlam'):
        if member is None:
            return fallback
        return member.display_name


async def send_phrase_reply(channel, automatic=False):
    """Send one learned phrase reply. Module-level so other cogs can call it."""
    from cogs.core import theatrical_channel_send
    if automatic and S.is_bedtime():
        return None
    if random.random() < S.SILENCE_CHANCE:
        S.debug('Silence roll triggered')
        return None
    if random.random() < 0.25:
        possible_commands = ['/beg', '/work', '/pray', '/gamble all']
        # Need a bot instance for history; fall back to a simple command
        from cogs.core import rogue_send
        chosen = random.choice(possible_commands)
        S.debug(f'Bot using command: {chosen}')
        if automatic and S.is_bedtime():
            return None
        await theatrical_channel_send(channel, chosen)
        return chosen
    if S.mode == 'track':
        source_pool = S.user_full_lines.get(S.track_target, [])[-S.MAX_RECENT_PHRASES:]
        if not source_pool:
            source_pool = S.user_pools.get(S.track_target, [])[-S.MAX_RECENT_PHRASES:]
        S.debug(f'Using TRACK full-line pool ({len(source_pool)})')
        if not source_pool:
            S.debug('No tracked full lines available')
            return None
        sentence = random.choice(source_pool)
        S.debug('Reply type: full line echo')
    else:
        source_pool = []
        for phrases in S.user_pools.values():
            source_pool.extend(phrases[-S.MAX_RECENT_PHRASES:])
        S.debug(f'Using GLOBAL pool ({len(source_pool)})')
        if not source_pool:
            sentence = random.choice(S.FALLBACKS)
            S.debug('Using fallback')
        else:
            roll = random.random()
            S.debug(f'Reply roll: {roll:.2f}')
            if roll < 0.25:
                sentence = random.choice(source_pool)
                S.debug('Reply type: direct echo')
            elif roll < 0.5:
                sentence = S.generate_learned_reaction() or random.choice(source_pool)
                S.debug('Reply type: learned reaction')
            elif roll < 0.8:
                count = random.randint(2, S.MAX_REPLY_PHRASES)
                parts = random.sample(source_pool, min(count, len(source_pool)))
                sentence = ' '.join(parts)
                S.debug(f'Reply type: mash ({count})')
            elif len(source_pool) >= 2:
                a, b = random.sample(source_pool, 2)
                sentence = S.remix_phrase(a, b)
                S.debug('Reply type: remix')
            else:
                sentence = source_pool[0]
    sentence = S.personality_text(sentence)
    if sentence in S.recent_sentences:
        S.debug('Sentence rejected (recent duplicate)')
        return None
    S.recent_sentences.append(sentence)
    if len(S.recent_sentences) > S.MAX_RECENT_SENTENCES:
        S.recent_sentences.pop(0)
    S.debug(f'Sending: {sentence}')
    S.bot_stats['replies_sent'] += 1
    await S.save_cash_data()
    if automatic and S.is_bedtime():
        return None
    await theatrical_channel_send(channel, sentence)
    return sentence


async def setup(bot):
    await bot.add_cog(Fun(bot))
