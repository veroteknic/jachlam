# Jachlam — instructions for future OpenCode instances

## Mandatory on every functional change (no exceptions)
1. Bump `JACHLAM_VERSION` in `cogs/state.py` (date + next `rNN`).
2. Prepend a `CHANGELOG_PAGES.insert(0, {...})` entry describing the change.
3. Verify with `uv run python -m py_compile bot.py` (and import check if touched).

## Slash-command cap (hard limit)
- Discord allows ~100 global slash commands. This repo sits at 51 (`grep -rc "@commands.hybrid_command" cogs/*.py | grep -v ":0"`).
- NEVER add `@commands.hybrid_command`. New commands MUST be manual `!`-prefix handlers following the `check_prefix_admin_commands` pattern in `cogs/admin.py` (parse in `on_message`, return True if handled).
- After any edit, confirm the hybrid count is unchanged.

## Safety invariants
- `PROTECTED_USER_IDS` users can never be harmed: no steal/assassinate/bounty/trial/expunge/silence/quarantine/cash-take/debt-give/tax/wanted against them. Every new harmful path must check `is_protected()`.
- Cash read-modify-write must use `modify_cash` / `debit_cash` / `set_cash_locked` (per-user locks), never raw `get_cash` + `set_cash` across awaits.
- `!` admin commands must enforce permissions (`_prefix_is_admin` for economy/system, `_prefix_has` with the matching Discord perm for moderation) and reply `not allowed` on denial.
- `on_message` order matters: execution toggle → death gate → silence enforce → epstein/silence/roleguard/prefix-admin checks → quarantine enforce → activity/channel gating.

## Docker deploy (this repo runs in Docker)
- Deploy with `./deploy.sh` (container `jachlam`, volume `jachlam-data`, image `jachlam-bot:latest`). Do NOT just `docker build` — `/app` is a named volume, so a rebuild alone changes nothing about the running bot.
- `deploy.sh` snapshots live data files out of the container first; live data always wins over host files on redeploy.
- Runtime data files the bot rewrites (must never be rolled back): `cash_data.json`, `inventory_data.json`, `markov_corpus.txt`, `seen_gifs.json`, `voicecast_data.json`, `death_data.json`, `epstein_data.json`, `silence_data.json`.
- Never bind-mount individual data files (`os.replace()` fails with EBUSY on bind-mounted files and saves fail silently).
- After deploy, check the boot log: `docker logs jachlam 2>&1 | grep -iE "VOICE CASTING|SLASH COMMANDS|READY"`.
- Local `uv run python ...` is fine for syntax/import checks, but the bot itself runs via Docker.
