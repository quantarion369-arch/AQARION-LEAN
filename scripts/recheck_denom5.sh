#!/usr/bin/env bash
cd /root/AQARION_MARKOV_MEMORY_LEAN || { echo "STOP: project dir"; exit 1; }
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.35.0-rc4/bin/lean
TS=$(date -u +%Y%m%dT%H%M%SZ)
D="$PWD/recheck_$TS"
mkdir "$D" || { echo "STOP: cannot create $D"; exit 1; }
SUMMARY="$D/SUMMARY.txt"

CHAIN="
Denom5InvariantPlaneFixed
Denom5RationalSpan
Denom5KernelCriterionFixed
Denom5SpanClosure
Denom5SpanMinimality
Denom5ObservableDynamics
Denom5ExplicitObservedFixed
Denom5FiniteWordSimulationCore2
Denom5CylinderProbabilityFixed
Denom5PitmanRogersLink
Denom5BalancedInitialCylinderFixed
Denom5WeakLumpabilityAlgebra
Denom5WeakLumpabilityProbability
Denom5WeakLumpabilityTwoStep
Denom5ObservedAllHistoryMarkov
Denom5BalancedAllHistoryMarkov
Denom5WeakLumpabilityCapstone
"
EXTRA="Denom5WeakLumpabilityFiniteHistory"

{
  echo "AQARION DENOM5 FROM-SOURCE REBUILD CHECK"
  echo "UTC=$TS"
  "$LEAN" --version
  echo "LEAN_PATH restricted to: $D"
  echo
} > "$SUMMARY"

OK=1
build_one () {
  m="$1"; tag="$2"
  LEAN_PATH="$D" timeout --kill-after=5s 300s "$LEAN" -j1 \
    -o "$D/$m.olean" "$m.lean" > "$D/$m.log" 2>&1
  st=$?
  sorryAx=$(grep -c 'sorryAx' "$D/$m.log")
  usesSorry=$(grep -c "declaration uses 'sorry'" "$D/$m.log")
  axioms=$(grep -c 'depends on axioms' "$D/$m.log")
  if [ "$st" -ne 0 ]; then
    res="BUILD_FAILED"
  elif [ -f "$m.olean" ] && cmp -s "$D/$m.olean" "$m.olean"; then
    res="OBJECT_IDENTICAL"
  else
    res="OBJECT_DIFFERS_OR_NO_ORIGINAL"
  fi
  printf '%s %-38s exit=%s axioms_lines=%s sorryAx=%s usesSorry=%s src=%s obj=%s\n' \
    "$tag" "$m" "$st" "$axioms" "$sorryAx" "$usesSorry" \
    "$(sha256sum "$m.lean" | cut -c1-16)" \
    "$( [ -f "$D/$m.olean" ] && sha256sum "$D/$m.olean" | cut -c1-16 || echo none )" \
    >> "$SUMMARY"
  printf '    result=%s\n' "$res" >> "$SUMMARY"
  [ "$st" -eq 0 ]
}

for m in $CHAIN; do
  if [ "$OK" -eq 1 ]; then
    build_one "$m" "[CHAIN]" || OK=0
  else
    echo "[CHAIN] $m SKIPPED (earlier module failed)" >> "$SUMMARY"
  fi
done

if [ "$OK" -eq 1 ]; then
  build_one "$EXTRA" "[EXTRA-NOT-COUNTED]"
fi

echo >> "$SUMMARY"
echo "CHAIN_ALL_BUILT=$OK" >> "$SUMMARY"
cat "$SUMMARY"
sha256sum "$SUMMARY"
