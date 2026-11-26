#!/usr/bin/env bash
cd /root/AQARION_MARKOV_MEMORY_LEAN || { echo "STOP: project dir missing"; exit 1; }

LEAN=/root/.elan/toolchains/leanprover--lean4---v4.35.0-rc4/bin/lean
TS=$(date -u +%Y%m%dT%H%M%SZ)
OUT="Denom5_MANIFEST_${TS}.txt"
[ -e "$OUT" ] && { echo "STOP: $OUT exists"; exit 1; }

ACCEPTED="
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

{
  echo "AQARION DENOM5 EVIDENCE MANIFEST"
  echo "UTC=$TS"
  echo "HOST=$(uname -m)"
  "$LEAN" --version
  echo
  echo "NOTE: the ACCEPTED list below comes from build receipts pasted"
  echo "during the session (exit 0, no sorryAx). Axioms reported:"
  echo "propext, Classical.choice, Quot.sound. Not axiom-free."
  echo

  n=0; missing=0
  for m in $ACCEPTED; do
    n=$((n+1))
    echo "[$m]  status=ACCEPTED_LISTED"
    if [ -f "$m.lean" ]; then sha256sum "$m.lean"; else echo "MISSING_SOURCE $m.lean"; missing=$((missing+1)); fi
    if [ -f "$m.olean" ]; then sha256sum "$m.olean"; else echo "MISSING_OBJECT $m.olean"; missing=$((missing+1)); fi
    r="${m}_compile_receipt.txt"
    if [ -f "$r" ]; then sha256sum "$r"; else echo "NO_SEPARATE_RECEIPT_FILE"; fi
    if [ -f "$m.lean" ]; then
      echo "sorry_count=$(grep -c '\bsorry\b' "$m.lean")"
      echo "axiom_decl_count=$(grep -cE '^axiom ' "$m.lean")"
    fi
    echo
  done

  echo "ACCEPTED_LISTED_MODULES=$n"
  echo "MISSING_ARTIFACTS=$missing"
  echo
  echo "=== OTHER Denom5*.lean FILES (NOT IN ACCEPTED LIST: TREAT AS NOT ACCEPTED) ==="
  for f in Denom5*.lean; do
    b="${f%.lean}"
    case " $(echo $ACCEPTED) " in
      *" $b "*) ;;
      *) echo "[$b]  status=NOT_ACCEPTED"; sha256sum "$f"
         if [ -f "$b.olean" ]; then sha256sum "$b.olean"; else echo "NO_OBJECT"; fi
         echo ;;
    esac
  done
} > "$OUT" 2>&1

echo "WROTE: $OUT"
sha256sum "$OUT"
wc -l "$OUT"
