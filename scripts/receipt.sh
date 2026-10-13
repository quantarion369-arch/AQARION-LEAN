#!/usr/bin/env bash
set -u
PROJ="${1:?Usage: scripts/receipt.sh PROJECT}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
[ -d "$ROOT/$PROJ" ] || { echo "No such project: $PROJ"; exit 1; }

STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="$ROOT/RECEIPTS/${PROJ}-${STAMP}.txt"

{
  echo "=== $PROJ REBUILD RECEIPT ==="
  date -u
  echo "Git commit: $(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo none)"
  echo "Toolchain: $(cat "$ROOT/$PROJ/lean-toolchain" 2>/dev/null || echo unspecified)"
  echo
  echo "=== SOURCE HASHES ==="
  find "$ROOT/$PROJ" -type f -name '*.lean' -not -path '*/.lake/*' \
    -print0 | sort -z | xargs -0 sha256sum || true
  echo
  echo "=== BUILD ==="
  cd "$ROOT/$PROJ"
  lake build 2>&1
  EXIT=$?
  echo "${PROJ}_BUILD_EXIT=$EXIT"
  exit "$EXIT"
} > "$OUT" 2>&1

EXIT=$?
echo "Wrote $OUT"
exit "$EXIT"
