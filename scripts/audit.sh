#!/usr/bin/env bash
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "=== AQARION LEAN AUDIT ==="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo

for PROJ in AQFPR006 PB006Audit PBCore006; do
  if [ -d "$ROOT/$PROJ" ]; then
    echo "--- $PROJ ---"
    grep -RInE '\b(sorry|admit|native_decide)\b' \
      --include='*.lean' "$ROOT/$PROJ" || echo "clean"
    echo
  fi
done

echo "=== RECEIPTS ==="
find "$ROOT/RECEIPTS" -maxdepth 1 -type f -printf '%f
' 2>/dev/null | sort
