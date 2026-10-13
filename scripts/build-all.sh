#!/usr/bin/env bash
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$ROOT/RECEIPTS"
FAIL=0

for PROJ in AQFPR006 PB006Audit PBCore006; do
  if [ ! -d "$ROOT/$PROJ" ]; then
    echo "SKIP $PROJ: not present"
    continue
  fi

  LOG="$ROOT/RECEIPTS/${PROJ}-${STAMP}.log"
  echo "=== BUILD $PROJ ===" | tee "$LOG"

  cd "$ROOT/$PROJ"
  lake build >> "$LOG" 2>&1
  EXIT=$?
  echo "${PROJ}_BUILD_EXIT=$EXIT" >> "$LOG"
  echo "$PROJ exit=$EXIT log=$LOG"

  if [ "$EXIT" -ne 0 ]; then
    FAIL=1
  fi

  cd "$ROOT"
done

echo "OVERALL_EXIT=$FAIL"
exit "$FAIL"
