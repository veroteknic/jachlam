"""Jachlam — Discord economy, moderation, and Markov bot.

Entry point: creates the bot, loads all cogs, and runs.
"""

import asyncio
import os
import sys

import discord
from discord.ext import commands

from cogs import state as S

intents = discord.Intents.default()
intents.message_content = True
intents.members = True
intents.presences = True

bot = commands.Bot(command_prefix=(), intents=intents, help_command=None)

COGS = [
    'cogs.core',
    'cogs.economy',
    'cogs.shop',
    'cogs.moderation',
    'cogs.admin',
    'cogs.fun',
    'cogs.helldivers',
]


async def load_cogs():
    for cog in COGS:
        try:
            await bot.load_extension(cog)
            print(f'[COG] loaded {cog}')
        except Exception as exc:
            print(f'[COG] FAILED to load {cog}: {exc}')
            raise


async def async_main():
    await load_cogs()
    await bot.start(S.TOKEN)


def main():
    if not S.TOKEN:
        print('[FATAL] No token found. Set DISCORD_TOKEN or TOKEN in your environment variables.')
        sys.exit(1)
    try:
        asyncio.run(async_main())
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
