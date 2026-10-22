#!/usr/bin/env bash
# Deploy the jachlam bot without losing data.
#
# /app is a named volume, so `docker build` alone changes nothing about the
# running bot: the container reads the copy inside the volume. This script
# rebuilds the image, pushes the code AND the live data files into the volume,
# then recreates the container. Mounting individual data files instead of the
# whole directory is deliberately avoided, because os.replace() fails with
# EBUSY on a bind-mounted file and every save would fail silently.

set -euo pipefail

CONTAINER="${CONTAINER:-jachlam}"
VOLUME="${VOLUME:-jachlam-data}"
IMAGE="${IMAGE:-jachlam-bot:latest}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Files the bot rewrites at runtime. These must be pushed into the volume, not
# just baked into the image, or a redeploy would roll the data backwards.
DATA_FILES=(
  cash_data.json
  inventory_data.json
  markov_corpus.txt
  seen_gifs.json
  voicecast_data.json
  death_data.json
  epstein_data.json
  silence_data.json
)

echo "==> stopping $CONTAINER"
docker exec "$CONTAINER" touch /app/deadman_paused 2>/dev/null || true
docker stop "$CONTAINER" >/dev/null 2>&1 || true

echo "==> snapshotting live data out of the container"
SNAP="$(mktemp -d)"
for f in "${DATA_FILES[@]}"; do
  docker cp "$CONTAINER:/app/$f" "$SNAP/$f" 2>/dev/null && echo "    pulled $f" || true
done
docker cp "$CONTAINER:/app/." "$SNAP/app" 2>/dev/null || true

echo "==> building $IMAGE"
docker build -t "$IMAGE" "$DIR" >/dev/null

if ! docker volume inspect "$VOLUME" >/dev/null 2>&1; then
  echo "==> seeding new volume $VOLUME from the image"
  docker run --rm -v "$VOLUME:/data" "$IMAGE" sh -c 'cp -a /app/. /data/'
fi

echo "==> pushing code and data into $VOLUME"
docker run --rm -v "$VOLUME:/app" -v "$DIR:/src:ro" "$IMAGE" sh -c '
  set -e
  cp -r /src/bot.py /src/lamjach.py /src/deadman.py /src/jachlam_voicecast_download.py /src/characters.txt /src/cogs /app/
'

# Live data wins over whatever is in the build context: the files pulled from
# the running container are newer than anything on the host.
echo "==> restoring live data into $VOLUME"
docker run --rm -v "$VOLUME:/app" -v "$SNAP:/snap:ro" "$IMAGE" sh -c '
  for f in '"${DATA_FILES[*]}"'; do
    [ -f "/snap/$f" ] && cp "/snap/$f" "/app/$f" || true
  done
'

echo "==> recreating $CONTAINER"
docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
docker run -d --name "$CONTAINER" --restart unless-stopped \
  -e PYTHONUNBUFFERED=1 -v "$VOLUME:/app" "$IMAGE" >/dev/null

echo "==> done; checking the boot log"
sleep 25
docker logs "$CONTAINER" 2>&1 | grep -iE "VOICE CASTING|SLASH COMMANDS|READY" || true

echo "==> lifting deadman maintenance pause"
docker exec "$CONTAINER" rm -f /app/deadman_paused 2>/dev/null || true

if docker inspect jachlam-deadman >/dev/null 2>&1; then
  echo "==> retiring same-token deadman watchdog (superseded by lamjach)"
  docker rm -f jachlam-deadman >/dev/null 2>&1 || true
fi

echo "==> (re)creating lamjach mirror twin on the new image"
docker rm -f lamjach >/dev/null 2>&1 || true
# NOTE: lamjach.py is bind-mounted from the host (not copied into the volume
# like bot.py) because the lamjach container runs /app from the IMAGE, not
# the volume -- without this it silently runs a stale copy (this exact drift
# caused a 30s hot-reconnect loop that got the token rate-limited/reset).
docker run -d --name lamjach --restart unless-stopped \
  -v "$VOLUME:/data" -v "$DIR/.env:/run/discord.env:ro" \
  -v "$DIR/lamjach.py:/app/lamjach.py:ro" \
  "$IMAGE" /app/.venv/bin/python /app/lamjach.py >/dev/null
echo "==> lamjach mirror recreated (needs LAMJACH_TOKEN in .env)"

rm -rf "$SNAP"
