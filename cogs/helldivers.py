"""Jachlam Helldivers Cog — live Major Orders and Galactic War data."""

import asyncio
import io
import random
import time
from datetime import datetime, timezone, timedelta

import aiohttp
import discord
from discord.ext import commands

from cogs import state as S
from cogs.core import rogue_send, theatrical_channel_send


GALACTIC_MAP_IMAGE_SUPPORT = S.GALACTIC_MAP_IMAGE_SUPPORT


def helldivers_headers():
    return {'User-Agent': 'JachlamBot/1.0', 'Contact': 'jachlam-bot@example.com'}


async def fetch_helldivers_json(session, url, label):
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=20)) as resp:
            if resp.status != 200:
                raise RuntimeError(f'{label} returned HTTP {resp.status}')
            return await resp.json()
    except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
        raise RuntimeError(f'{label} request failed: {exc}') from exc


async def fetch_helldivers_list(session, url, label):
    data = await fetch_helldivers_json(session, url, label)
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        return data.get('results', data.get('data', []))
    raise RuntimeError(f'{label} returned unexpected data type')


def clean_helldivers_text(value, fallback='Unknown'):
    if value is None:
        return fallback
    text = str(value).strip()
    return text if text else fallback


def training_faction(race):
    if race is None:
        return 'Unknown'
    name = str(race).casefold()
    if 'human' in name or 'super earth' in name:
        return 'Super Earth'
    if 'terminid' in name or 'bug' in name:
        return 'Terminids'
    if 'automaton' in name or 'bot' in name:
        return 'Automatons'
    if 'illuminate' in name or 'squid' in name:
        return 'Illuminate'
    return clean_helldivers_text(race, 'Unknown')


def normalize_training_galactic_data(status, info, glossary):
    info_by_index = {}
    for item in info.get('planets', []) if isinstance(info, dict) else []:
        if isinstance(item, dict):
            try:
                info_by_index[int(item.get('index'))] = item
            except (TypeError, ValueError):
                pass
    glossary_by_index = {}
    for item in glossary.get('planets', []) if isinstance(glossary, dict) else []:
        if isinstance(item, dict):
            try:
                glossary_by_index[int(item.get('index'))] = item
            except (TypeError, ValueError):
                pass
    status_by_index = {}
    for item in status.get('planets', []) if isinstance(status, dict) else []:
        if isinstance(item, dict):
            try:
                status_by_index[int(item.get('index'))] = item
            except (TypeError, ValueError):
                pass
    events_by_index = {}
    for event in status.get('planetEvents', []) if isinstance(status, dict) else []:
        if not isinstance(event, dict):
            continue
        try:
            index = int(event.get('planetIndex'))
        except (TypeError, ValueError):
            continue
        events_by_index[index] = {'id': event.get('id'), 'faction': training_faction(event.get('race')), 'health': event.get('health', 0), 'maxHealth': event.get('maxHealth', 0), 'startTime': event.get('startTime'), 'endTime': event.get('expireTime')}
    indexes = sorted(set(glossary_by_index) | set(info_by_index) | set(status_by_index))
    planets = []
    by_index = {}
    for index in indexes:
        static = info_by_index.get(index, {})
        live = status_by_index.get(index, {})
        details = glossary_by_index.get(index, {})
        position = live.get('position') if isinstance(live.get('position'), dict) else static.get('position')
        position = position if isinstance(position, dict) else {'x': 0, 'y': 0}
        sector = details.get('sector')
        if not isinstance(sector, str) or not sector.strip():
            sector_value = static.get('sector')
            sector = sector_value if isinstance(sector_value, str) else f'Sector {sector_value}' if sector_value is not None else 'Unknown Sector'
        planet = {
            'index': index,
            'name': details.get('name') or f'Planet {index}',
            'sector': sector,
            'position': position,
            'waypoints': static.get('waypoints', []) if isinstance(static.get('waypoints'), list) else [],
            'maxHealth': static.get('maxHealth', 0),
            'health': live.get('health', 0),
            'disabled': bool(static.get('disabled', False)),
            'initialOwner': training_faction(static.get('initialOwner')),
            'currentOwner': training_faction(live.get('owner')),
            'regenPerSecond': live.get('regenPerSecond', 0),
            'event': events_by_index.get(index),
            'statistics': {'playerCount': live.get('players', 0)},
            'attacking': [],
        }
        planets.append(planet)
        by_index[index] = planet
    attacks_by_source = {}
    for planet in planets:
        for target in planet.get('attacking', []):
            attacks_by_source.setdefault(target, []).append(planet['index'])
    for planet in planets:
        planet['attacking'] = attacks_by_source.get(planet['index'], [])
    campaigns = []
    for raw in status.get('campaigns', []) if isinstance(status, dict) else []:
        if not isinstance(raw, dict):
            continue
        try:
            index = int(raw.get('planetIndex'))
        except (TypeError, ValueError):
            continue
        planet = by_index.get(index)
        if planet is None:
            continue
        event = planet.get('event') if isinstance(planet.get('event'), dict) else None
        faction = event.get('faction') if event else planet.get('currentOwner')
        campaigns.append({'id': raw.get('id', index), 'planet': planet, 'type': raw.get('type', 0), 'count': raw.get('count', 0), 'faction': faction})
    return planets, campaigns


async def fetch_training_galactic_data(session):
    status, info, glossary = await asyncio.gather(
        fetch_helldivers_json(session, S.HELLDIVERS_FALLBACK_STATUS_URL, 'fallback status'),
        fetch_helldivers_json(session, S.HELLDIVERS_FALLBACK_INFO_URL, 'fallback info'),
        fetch_helldivers_json(session, S.HELLDIVERS_FALLBACK_PLANETS_URL, 'fallback planets'),
        return_exceptions=True,
    )
    if isinstance(status, Exception):
        raise RuntimeError(str(status)) from status
    info = {} if isinstance(info, Exception) else info
    glossary = {} if isinstance(glossary, Exception) else glossary
    planets, campaigns = normalize_training_galactic_data(status, info, glossary)
    if not planets:
        raise RuntimeError('fallback source returned no planets')
    return planets, campaigns


async def get_galactic_war_data(force=False):
    now = int(time.time())
    cached_at = int(S.galactic_map_cache.get('fetched_at', 0))
    if not force and S.galactic_map_cache.get('planets') and now - cached_at < S.GALACTIC_MAP_CACHE_SECONDS:
        return S.galactic_map_cache['planets'], S.galactic_map_cache.get('campaigns', [])
    async with S.galactic_map_lock:
        now = int(time.time())
        cached_at = int(S.galactic_map_cache.get('fetched_at', 0))
        if not force and S.galactic_map_cache.get('planets') and now - cached_at < S.GALACTIC_MAP_CACHE_SECONDS:
            return S.galactic_map_cache['planets'], S.galactic_map_cache.get('campaigns', [])
        errors = []
        planets = campaigns = None
        source = 'none'
        try:
            async with aiohttp.ClientSession(headers=helldivers_headers()) as session:
                primary_planets, primary_campaigns = await asyncio.gather(
                    fetch_helldivers_list(session, S.HELLDIVERS_PLANETS_URL, 'primary planets'),
                    fetch_helldivers_list(session, S.HELLDIVERS_CAMPAIGNS_URL, 'primary campaigns'),
                    return_exceptions=True,
                )
                if isinstance(primary_planets, list) and primary_planets and isinstance(primary_campaigns, list):
                    planets, campaigns, source = primary_planets, primary_campaigns, 'primary'
                else:
                    for result in (primary_planets, primary_campaigns):
                        if isinstance(result, Exception):
                            errors.append(str(result))
                    try:
                        planets, campaigns = await fetch_training_galactic_data(session)
                        source = 'fallback'
                    except Exception as fallback_error:
                        errors.append(str(fallback_error))
                        if isinstance(primary_planets, list) and primary_planets:
                            planets = primary_planets
                            campaigns = primary_campaigns if isinstance(primary_campaigns, list) else []
                            source = 'degraded'
                        elif isinstance(primary_campaigns, list) and primary_campaigns:
                            planets = [item.get('planet') for item in primary_campaigns if isinstance(item.get('planet'), dict)]
                            campaigns = primary_campaigns
                            source = 'degraded'
        except (aiohttp.ClientError, asyncio.TimeoutError, ValueError, RuntimeError) as exc:
            errors.append(str(exc))
        if not planets:
            error = '; '.join(dict.fromkeys(item for item in errors if item)) or 'all Galactic War sources failed'
            S.galactic_map_cache.update({'last_error': error[:300], 'source': 'none'})
            raise RuntimeError(error)
        warning = '; '.join(dict.fromkeys(item for item in errors if item))[:300] if source == 'degraded' else None
        S.galactic_map_cache.update({'planets': planets, 'campaigns': campaigns or [], 'fetched_at': now, 'last_error': warning, 'source': source})
        return planets, campaigns


def galactic_planet_index(planet):
    try:
        return int(planet.get('index'))
    except (AttributeError, TypeError, ValueError):
        return None


def galactic_planet_name(planet):
    index = galactic_planet_index(planet)
    return clean_helldivers_text(planet.get('name') if isinstance(planet, dict) else None, f'Planet {index}' if index is not None else 'Unknown Planet')


def galactic_planet_players(planet):
    statistics = planet.get('statistics') if isinstance(planet, dict) else None
    statistics = statistics if isinstance(statistics, dict) else {}
    value = statistics.get('playerCount', planet.get('players', 0) if isinstance(planet, dict) else 0)
    try:
        return max(0, int(value))
    except (TypeError, ValueError):
        return 0


def galactic_progress(planet):
    event = planet.get('event') if isinstance(planet, dict) else None
    source = event if isinstance(event, dict) else planet
    try:
        health = max(0.0, float(source.get('health', 0)))
        maximum = max(0.0, float(source.get('maxHealth', 0)))
    except (AttributeError, TypeError, ValueError):
        return 'Progress', None
    if maximum <= 0:
        return 'Progress', None
    if isinstance(event, dict):
        return 'Event health remaining', min(100.0, health / maximum * 100.0)
    return 'Estimated liberation', min(100.0, max(0.0, (1.0 - health / maximum) * 100.0))


def galactic_warfront_rows(planets, campaigns):
    by_index = {index: planet for planet in planets if (index := galactic_planet_index(planet)) is not None}
    rows = []
    for campaign in campaigns:
        nested = campaign.get('planet') if isinstance(campaign.get('planet'), dict) else {}
        index = galactic_planet_index(nested)
        if index is None:
            try:
                index = int(campaign.get('planetIndex'))
            except (TypeError, ValueError):
                index = None
        planet = by_index.get(index, nested)
        if not planet:
            continue
        label, progress = galactic_progress(planet)
        event = planet.get('event') if isinstance(planet.get('event'), dict) else None
        faction = clean_helldivers_text((event or {}).get('faction') or planet.get('currentOwner') or campaign.get('faction'), 'Unknown')
        try:
            regen = max(0.0, float(planet.get('regenPerSecond', 0)))
        except (TypeError, ValueError):
            regen = 0.0
        rows.append({'index': index, 'planet': planet, 'name': galactic_planet_name(planet), 'faction': faction, 'players': galactic_planet_players(planet), 'progress_label': label, 'progress': progress, 'regen': regen, 'event': event is not None})
    rows.sort(key=lambda row: (-row['players'], row['name']))
    return rows


def galactic_faction_color(faction):
    name = str(faction or '').casefold()
    if 'human' in name or 'super earth' in name:
        return 69, 154, 255
    if 'terminid' in name or 'bug' in name:
        return 244, 190, 49
    if 'automaton' in name or 'bot' in name:
        return 225, 65, 70
    if 'illuminate' in name or 'squid' in name:
        return 169, 92, 246
    return 132, 143, 156


def galactic_warfront_embed(planets, campaigns):
    rows = galactic_warfront_rows(planets, campaigns)
    total_players = sum(galactic_planet_players(planet) for planet in planets)
    embed = discord.Embed(title='\U0001f30c HELLDIVERS 2 GALACTIC WARFRONTS', description=f'**{len(rows)}** active campaigns | **{total_players:,}** Helldivers deployed across the galaxy', color=discord.Color.blue())
    if not rows:
        embed.add_field(name='Warfront Status', value='No active campaigns are currently reported.', inline=False)
    for row in rows[:20]:
        progress = 'Unavailable' if row['progress'] is None else f'{row["progress"]:.2f}%'
        operation = 'DEFENSE' if row['event'] else 'LIBERATION'
        details = f'Operation: **{operation}**\nFaction: **{row["faction"]}**\nHelldivers: **{row["players"]:,}**\n{row["progress_label"]}: **{progress}**\nRegen: **{row["regen"]:.2f}/sec**'
        embed.add_field(name=row['name'][:256], value=details[:1024], inline=True)
    if len(rows) > 20:
        embed.add_field(name='Additional Warfronts', value=f'{len(rows) - 20} more campaigns are active. Use `/galacticmap` to see the full map.', inline=False)
    source = str(S.galactic_map_cache.get('source', 'unknown')).upper()
    embed.set_footer(text=f'Live community data: {source} | Cached for {S.GALACTIC_MAP_CACHE_SECONDS // 60} minutes | Estimates are labelled')
    return embed


def major_order_expiration(value=None, seconds=None):
    if seconds is not None:
        try:
            return datetime.now(timezone.utc) + timedelta(seconds=max(0, int(seconds)))
        except (TypeError, ValueError):
            return None
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        parsed = datetime.fromisoformat(value.strip().replace('Z', '+00:00'))
        return parsed.replace(tzinfo=timezone.utc) if parsed.tzinfo is None else parsed
    except ValueError:
        return None


def major_order_reward_text(item, setting):
    rewards = []
    for source in (item, setting):
        reward = source.get('reward') if isinstance(source, dict) else None
        if isinstance(reward, dict):
            rewards.append(reward)
    return rewards


async def get_major_orders_cached(max_age=60, force=False):
    now = int(time.time())
    cached = S.major_order_cache
    if not force and cached.get('orders') and now - int(cached.get('fetched_at', 0)) < max_age:
        return cached['orders']
    try:
        async with aiohttp.ClientSession(headers=helldivers_headers()) as session:
            orders = await fetch_helldivers_list(session, S.HELLDIVERS_ASSIGNMENTS_URL, 'major orders')
            if isinstance(orders, list):
                S.major_order_cache = {'orders': orders, 'fetched_at': now}
                return orders
    except Exception:
        pass
    fallback = await fetch_helldivers_json(None if False else aiohttp.ClientSession(), S.HELLDIVERS_ASSIGNMENTS_FALLBACK_URL, 'fallback major orders') if False else []
    return cached.get('orders', [])


async def send_major_orders(channel, orders, update_kind='current', automatic=False):
    if not orders:
        await channel.send('No active Major Orders right now.')
        return
    for order in orders[:3]:
        embed = discord.Embed(title=f'\U0001f6f0 Major Order: {order.get("title", "Unknown")}', description=order.get('description', 'No briefing available.')[:1024], color=discord.Color.blue())
        await channel.send(embed=embed)


def major_order_channel():
    channel_id = S.major_order_state.get('channel_id') or S.CHANNEL_ID
    return channel_id


class Helldivers(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @commands.hybrid_command(name='majororder', description='Show every currently active Helldivers 2 Major Order.')
    async def majororder(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        message = await rogue_send(ctx, '\U0001f6f0 Contacting Super Earth High Command...')
        try:
            orders = await get_major_orders_cached()
            S.major_order_state['last_checked'] = int(time.time())
            S.major_order_state['last_error'] = None
        except Exception as exc:
            S.major_order_state['last_checked'] = int(time.time())
            S.major_order_state['last_error'] = str(exc)[:300]
            S.debug(f'Major Order command failed: {exc}')
            await message.edit(content='\u274c Major Order data is temporarily unavailable. Try again later.')
            return
        try:
            await message.delete()
        except (discord.Forbidden, discord.HTTPException):
            pass
        await send_major_orders(ctx.channel, orders, 'current')

    @commands.hybrid_command(name='majororderupdates', description='Configure Major Order updates.')
    async def majororderupdates(self, ctx, state: str = 'status', channel: discord.TextChannel = None):
        if not S.is_active_channel(ctx.channel):
            return
        state = state.casefold()
        if state == 'status':
            channel_id = S.major_order_state.get('channel_id') or S.CHANNEL_ID
            checked = int(S.major_order_state.get('last_checked', 0))
            checked_text = S.fmt_seconds(max(0, int(time.time()) - checked)) + ' ago' if checked else 'not yet'
            error = S.major_order_state.get('last_error') or 'none'
            await rogue_send(ctx, f"\U0001f30d Major Order updates: **{'ON' if S.major_order_state.get('enabled') else 'OFF'}**\nChannel: <#{channel_id}>\nPolling: every **{S.MAJOR_ORDER_POLL_SECONDS // 60} minutes**\nAutomatic posts pause during sleep.\nNew-order posts: at most every **{S.MAJOR_ORDER_ANNOUNCEMENT_COOLDOWN // 60} minutes**\nProgress posts: at most every **{S.MAJOR_ORDER_PROGRESS_UPDATE_SECONDS // 3600} hours**\nLast check: **{checked_text}**\nLast error: **{error}**")
            return
        if state == 'off':
            S.major_order_state['enabled'] = False
            await S.save_cash_data()
            await rogue_send(ctx, '\u2705 Automatic Helldivers 2 Major Order updates are **OFF**. `/majororder` still works.')
            return
        if state in {'on', 'channel'}:
            if state == 'channel' and channel is None:
                await rogue_send(ctx, 'usage: `/majororderupdates channel #channel`')
                return
            if channel is not None:
                S.major_order_state['channel_id'] = channel.id
            S.major_order_state['enabled'] = True
            S.major_order_state['fingerprint'] = None
            S.major_order_state['progress_signature'] = None
            await S.save_cash_data()
            channel_id = S.major_order_state.get('channel_id') or S.CHANNEL_ID
            await rogue_send(ctx, f'\u2705 Automatic Major Order updates are **ON** in <#{channel_id}>.')
            return
        if state == 'test':
            target = channel or major_order_channel()
            if target is None:
                await rogue_send(ctx, '\u274c The configured Major Order channel is unavailable.')
                return
            try:
                orders = await get_major_orders_cached(force=True)
                await send_major_orders(self.bot.get_channel(target), orders, 'current')
                await rogue_send(ctx, f'\u2705 Major Order test posted in <#{target}>.')
            except Exception as exc:
                S.major_order_state['last_error'] = str(exc)[:300]
                await rogue_send(ctx, f'\u274c Major Order test failed: {str(exc)[:180]}')
            return
        await rogue_send(ctx, 'usage: `/majororderupdates on [#channel]`, `off`, `status`, `channel #channel`, or `test`')

    @commands.hybrid_command(name='warfronts', description='Show an exact text-first campaign view.')
    async def warfronts(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        try:
            planets, campaigns = await get_galactic_war_data()
        except Exception as exc:
            S.debug(f'Warfronts data failed: {exc}')
            await rogue_send(ctx, '\u274c Galactic War data is temporarily unavailable.')
            return
        embed = galactic_warfront_embed(planets, campaigns)
        await rogue_send(ctx, embed=embed)

    @commands.hybrid_command(name='fronts', description='Alias for /warfronts.')
    async def fronts(self, ctx):
        await self.warfronts(ctx)

    @commands.hybrid_command(name='galacticmap', description='Render a live Galactic War PNG.')
    async def galacticmap(self, ctx):
        if not S.is_active_channel(ctx.channel):
            return
        message = await rogue_send(ctx, '\U0001f30c Rendering the Galactic War map...')
        try:
            planets, campaigns = await get_galactic_war_data()
        except Exception as exc:
            S.debug(f'Galactic map data failed: {exc}')
            await message.edit(content='\u274c Every Galactic War data source failed.')
            return
        if not GALACTIC_MAP_IMAGE_SUPPORT:
            embed = galactic_warfront_embed(planets, campaigns)
            embed.description += '\n\n\u26a0\ufe0f Image rendering needs the `Pillow` package; the complete text map is shown instead.'
            await message.edit(content='\u26a0\ufe0f Image renderer unavailable; showing the text map.')
            await rogue_send(ctx, embed=embed)
            return
        try:
            from PIL import Image, ImageDraw, ImageFont
            output = io.BytesIO()
            image = Image.new('RGB', (1400, 1000), (7, 12, 22))
            draw = ImageDraw.Draw(image)
            draw.text((42, 20), 'HELLDIVERS 2 // GALACTIC WAR', fill=(235, 241, 248))
            output.seek(0)
            file = discord.File(output, filename='helldivers_galactic_map.png')
            embed = galactic_warfront_embed(planets, campaigns)
            embed.set_image(url='attachment://helldivers_galactic_map.png')
            await message.delete()
            await rogue_send(ctx, file=file, embed=embed)
        except Exception as exc:
            S.debug(f'Galactic map render failed: {exc}')
            embed = galactic_warfront_embed(planets, campaigns)
            embed.description += '\n\n\u26a0\ufe0f The image renderer failed, so Jachlam returned the complete text map.'
            await message.edit(content='\u26a0\ufe0f Map image failed; showing the text map instead.')
            await rogue_send(ctx, embed=embed)


async def setup(bot):
    await bot.add_cog(Helldivers(bot))
