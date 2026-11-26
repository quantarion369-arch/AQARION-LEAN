#!/usr/bin/env bash
cd /root/AQARION_MARKOV_MEMORY_LEAN || { echo "STOP: project dir"; exit 1; }
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.35.0-rc4/bin/lean
ARCH="$PWD/denom5_evidence_20261126T053636Z.tar.gz"
WANT=b0662ae7f1befe5589f86d00ba6b7a7277fbcd519b38e5f254bd9c40a2eac653
GOT=$(sha256sum "$ARCH" | cut -d' ' -f1)
[ "$GOT" = "$WANT" ] || { echo "STOP: archive hash mismatch: $GOT"; exit 1; }

TS=$(date -u +%Y%m%dT%H%M%SZ)
V="/root/denom5_verify_$TS"
mkdir "$V" "$V/build" || { echo "STOP: mkdir"; exit 1; }
tar xzf "$ARCH" -C "$V" || { echo "STOP: extract failed"; exit 1; }
cd "$V" || exit 1
MAN=$(ls Denom5_MANIFEST_*.txt | head -1)
S="$V/VERIFY_SUMMARY.txt"
{ echo "ARCHIVE SELF-CONTAINED REBUILD"; echo "UTC=$TS"; "$LEAN" --version
  echo "archive_sha256=$GOT"; echo "claim_scope_sha256=$(sha256sum CLAIM_SCOPE_DENOM5_v2.md | cut -d' ' -f1)"
  echo "manifest=$MAN"; echo; } > "$S"

CHAIN="Denom5InvariantPlaneFixed Denom5RationalSpan Denom5KernelCriterionFixed Denom5SpanClosure Denom5SpanMinimality Denom5ObservableDynamics Denom5ExplicitObservedFixed Denom5FiniteWordSimulationCore2 Denom5CylinderProbabilityFixed Denom5PitmanRogersLink Denom5BalancedInitialCylinderFixed Denom5WeakLumpabilityAlgebra Denom5WeakLumpabilityProbability Denom5WeakLumpabilityTwoStep Denom5ObservedAllHistoryMarkov Denom5BalancedAllHistoryMarkov Denom5WeakLumpabilityCapstone"
OK=1; MATCH=0; TOTAL=0
for m in $CHAIN; do
  TOTAL=$((TOTAL+1))
  if [ "$OK" -ne 1 ]; then echo "$m SKIPPED" >> "$S"; continue; fi
  LEAN_PATH="$V/build" timeout --kill-after=5s 300s "$LEAN" -j1 -o "$V/build/$m.olean" "$m.lean" > "$V/build/$m.log" 2>&1
  st=$?
  have=$(sha256sum "$V/build/$m.olean" 2>/dev/null | cut -d' ' -f1)
  want=$(awk -v t="$m.olean" '$2==t{print $1}' "$MAN" | head -1)
  sx=$(grep -c sorryAx "$V/build/$m.log")
  if [ "$st" -eq 0 ] && [ -n "$want" ] && [ "$have" = "$want" ]; then r=MATCH; MATCH=$((MATCH+1)); else r=NOT_MATCH; fi
  [ "$st" -ne 0 ] && OK=0
  echo "$m exit=$st sorryAx=$sx $r" >> "$S"
done
echo >> "$S"; echo "MATCHED=$MATCH of $TOTAL" >> "$S"
cat "$S"; sha256sum "$S"
