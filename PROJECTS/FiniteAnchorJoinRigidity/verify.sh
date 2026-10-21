#!/usr/bin/env bash
set -euo pipefail

project=$(cd -- "$(dirname -- "$0")" && pwd)
cd "$project"

printf '%s
' \
'4c6ba80ea776a8ffc60702f567b24e878cec455ab594a539cefb5cd2a1b0c83b  AqarionAnchorBase.lean' \
'aee4d8d821de4cc46a94be4d027c0c9970e9c76104a87fca4135084313a6b09b  AqarionJoin.lean' |
sha256sum -c -

pin=leanprover/lean4:v4.35.0-rc4
test "$(cat lean-toolchain)" = "$pin"

if [ "${1:-}" = "--check-only" ]; then
    printf '%s
' 'SOURCE_HASHES_AND_TOOLCHAIN_PIN=PASS'
    exit 0
fi

export ELAN_TOOLCHAIN="$pin"
out=$(mktemp -d /tmp/finite-anchor-verify-XXXXXXXX)
export LEAN_PATH="$out"
log=

trap 'rc=$?; if [ "$rc" -ne 0 ]; then
    printf "VERIFICATION_FAILED: exit=%s directory=%s
" "$rc" "$out"
    if [ -n "$log" ] && [ -f "$log" ]; then
        tail -n 40 "$log"
    fi
fi' EXIT

cp AqarionAnchorBase.lean AqarionJoin.lean "$out/"
cd "$out"

cat > AxiomAudit.lean <<'AUDIT_SOURCE'
import AqarionJoin
#print axioms AqarionFiniteBridge.finite_quotient_pullback_rigidity
#print axioms AqarionAnchor.finite_anchor_rigidity
#print axioms AqarionJoin.join_universal_property
#print axioms AqarionJoin.finite_anchor_join_rigidity
AUDIT_SOURCE

cat > expected-axioms.log <<'EXPECTED_AXIOMS'
'AqarionFiniteBridge.finite_quotient_pullback_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AqarionAnchor.finite_anchor_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AqarionJoin.join_universal_property' does not depend on any axioms
'AqarionJoin.finite_anchor_join_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPECTED_AXIOMS

lean --version | tee context.txt
printf 'BUILD_DIRECTORY=%s
' "$out"

for module in AqarionAnchorBase AqarionJoin; do
    log="$out/$module.log"
    printf 'BUILDING=%s LOG=%s
' "$module" "$log"
    lean -j1 -M768 -DElab.async=false \
        -o "$module.olean" "$module.lean" > "$log" 2>&1
    test -s "$module.olean"
    printf 'BUILD_PASS=%s
' "$module"
done

log="$out/axioms.log"
printf '%s
' 'CHECKING_FOUR_AXIOM_REPORTS'
lean -j1 -M768 -DElab.async=false AxiomAudit.lean > "$log" 2>&1
diff -u expected-axioms.log "$log"
cat "$log"

printf '%s
' 'FINITE_ANCHOR_VERIFICATION=PASS'
printf 'BUILD_RECEIPT=%s
' "$out"
