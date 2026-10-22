"""Jachlam Backup Cog — manual backups, restore, and snapshot validation."""

import json
import os
import re
import shutil
from datetime import datetime

from cogs import state as S
from cogs.state import (
    CASH_FILE, INVENTORY_FILE, SEEN_GIFS_FILE, TEXT_FILE, CORE_BACKUP_FILES,
    PERSISTENT_FILES, BACKUP_DIR, JACHLAM_VERSION, atomic_save_json,
    _load_json_sync, inspect_persistent_file, list_manual_backups,
    resolve_backup_id, inspect_manual_backup, debug,
)


async def save_all_persistent():
    cash_ok = await S.save_cash_data()
    inventory_ok = await S.save_inventory_data()
    gifs_ok = await S.save_seen_gif_keys()
    return {'cash': bool(cash_ok), 'inventory': bool(inventory_ok), 'gifs': bool(gifs_ok)}


async def create_manual_backup(reason='manual', actor_id=None):
    saved = await save_all_persistent()
    if not all(saved.values()):
        failed = ', '.join(key for key, ok in saved.items() if not ok)
        raise RuntimeError(f'could not save {failed} before snapshot')
    os.makedirs(BACKUP_DIR, exist_ok=True)
    backup_id = _next_backup_id()
    destination = os.path.join(BACKUP_DIR, backup_id)
    temp_destination = os.path.join(BACKUP_DIR, f'.{backup_id}.tmp')
    os.makedirs(temp_destination)
    try:
        files = {}
        for filename, kind in PERSISTENT_FILES.items():
            if not os.path.exists(filename):
                continue
            target = os.path.join(temp_destination, filename)
            shutil.copy2(filename, target)
            info = inspect_persistent_file(target, kind)
            if not info['valid']:
                raise RuntimeError(f'{filename} failed validation: {info["status"]}')
            files[filename] = {'kind': kind, 'bytes': info['bytes'], 'sha256': info['sha256']}
        if not CORE_BACKUP_FILES.issubset(files):
            raise RuntimeError('snapshot is missing a core database')
        manifest = {
            'id': backup_id,
            'created_at': datetime.now(S.AWST).isoformat(),
            'version': JACHLAM_VERSION,
            'reason': str(reason),
            'actor_id': int(actor_id) if actor_id is not None else None,
            'files': files,
        }
        manifest_temp = os.path.join(temp_destination, 'manifest.json.tmp')
        with open(manifest_temp, 'w', encoding='utf-8') as f:
            json.dump(manifest, f, ensure_ascii=True, separators=(',', ':'))
        os.replace(manifest_temp, os.path.join(temp_destination, 'manifest.json'))
        os.replace(temp_destination, destination)
    except Exception:
        shutil.rmtree(temp_destination, ignore_errors=True)
        raise
    return inspect_manual_backup(backup_id)


async def restore_snapshot_files(backup_id):
    report = inspect_manual_backup(backup_id)
    if not report['valid']:
        raise RuntimeError('; '.join(report['errors']) or 'backup validation failed')
    cash_info = report['files'][CASH_FILE]
    if S.user_cash and cash_info.get('accounts', 0) == 0:
        raise RuntimeError('refusing to replace live balances with an empty backup')
    folder = report['folder']
    cash_payload = _load_json_sync(os.path.join(folder, CASH_FILE))
    inventory_payload = _load_json_sync(os.path.join(folder, INVENTORY_FILE))
    if not await S.atomic_save_json(CASH_FILE, cash_payload, S.cash_file_lock if hasattr(S, 'cash_file_lock') else __import__('asyncio').Lock(), 'cash restore'):
        raise RuntimeError('cash restore write failed')
    if not await S.atomic_save_json(INVENTORY_FILE, inventory_payload, S.inventory_file_lock if hasattr(S, 'inventory_file_lock') else __import__('asyncio').Lock(), 'inventory restore'):
        raise RuntimeError('inventory restore write failed')
    if SEEN_GIFS_FILE in report['files']:
        gif_payload = _load_json_sync(os.path.join(folder, SEEN_GIFS_FILE))
        if not await S.atomic_save_json(SEEN_GIFS_FILE, gif_payload, S.seen_gifs_file_lock if hasattr(S, 'seen_gifs_file_lock') else __import__('asyncio').Lock(), 'GIF restore'):
            raise RuntimeError('GIF restore write failed')
    if TEXT_FILE in report['files']:
        corpus_temp = f'{TEXT_FILE}.restore.tmp'
        shutil.copy2(os.path.join(folder, TEXT_FILE), corpus_temp)
        if os.path.exists(TEXT_FILE):
            shutil.copy2(TEXT_FILE, f'{TEXT_FILE}.bak')
        os.replace(corpus_temp, TEXT_FILE)
    await S.load_cash_data(allow_empty=False)
    await S.load_inventory_data()
    await S.load_seen_gif_keys()
    await S.load_corpus()
    return report


async def write_clean_exit_marker(backup_id):
    import aiofiles
    payload = {'backup_id': str(backup_id), 'created_at': datetime.now(S.AWST).isoformat(), 'version': JACHLAM_VERSION}
    temp_path = f'{S.CLEAN_EXIT_MARKER_FILE}.tmp'
    encoded = json.dumps(payload, ensure_ascii=True, separators=(',', ':'))
    async with aiofiles.open(temp_path, 'w', encoding='utf-8') as f:
        await f.write(encoded)
    os.replace(temp_path, S.CLEAN_EXIT_MARKER_FILE)


async def prepare_clean_exit(actor_id=None):
    if S.shutdown_started:
        raise RuntimeError('a shutdown is already in progress')
    S.shutdown_started = True
    try:
        report = await create_manual_backup('clean-exit automatic startup restore', actor_id)
        if not report['valid']:
            raise RuntimeError('clean-exit backup failed validation')
        await write_clean_exit_marker(report['id'])
    except Exception:
        S.shutdown_started = False
        raise
    return report


async def apply_pending_clean_exit_restore():
    if not os.path.exists(S.CLEAN_EXIT_MARKER_FILE):
        return None
    try:
        marker = _load_json_sync(S.CLEAN_EXIT_MARKER_FILE)
        if not isinstance(marker, dict) or not isinstance(marker.get('backup_id'), str):
            raise ValueError('clean-exit marker is invalid')
        backup_id = marker['backup_id']
        report = await restore_snapshot_files(backup_id)
        if not report['valid']:
            raise RuntimeError('clean-exit backup failed validation')
        os.remove(S.CLEAN_EXIT_MARKER_FILE)
        return backup_id
    except Exception as exc:
        raise RuntimeError(f'clean-exit automatic restore failed: {exc}') from exc


def _next_backup_id():
    base = datetime.now(S.AWST).strftime('%Y%m%d-%H%M%S')
    candidate = base
    suffix = 1
    while os.path.exists(os.path.join(BACKUP_DIR, candidate)):
        candidate = f'{base}-{suffix}'
        suffix += 1
    return candidate
