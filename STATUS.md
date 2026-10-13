# AQARION Lean Build Status

## Platform

- Android / Termux
- Ubuntu proot
- ARM64 ELF Lean binaries
- Lean 4.35.0-rc3
- Lake 5.0.0

## Build ledger

| Project | Status | Evidence |
|---|---|---|
| AQFPR006 | REBUILT / BASELINE GREEN / GATE 2 PASS | RECEIPTS/AQFPR006-receipt.txt, RECEIPTS/GATE2-RECEIPT.txt |
| PB006Audit | REBUILT / BASELINE GREEN | RECEIPTS/PB006Audit-rebuild.log |
| PBCore006 | SOURCE TRANSFERRED / BUILD PENDING | No current build receipt |

## AQFPR006 repair

- Replaced unavailable List.get! indexing with current bounded list indexing.
- Repaired rgs so an empty restricted-growth-string prefix emits only label 0.
- Verified partitions 3 produces exactly five set-partition structures.
- Verified anchors: weightedBell [1,1,2] = 7, [2,2] = 7, [2,2,2] = 31, [2,4] = 9, [3,3] = 8.

## Gate 2

Semantic gcd-to-lcm mutation:

    listGcd block -> block.foldl Nat.lcm 1

Result:

    BASELINE_BUILD_EXIT=0
    MUTATION_BUILD_EXIT=1
    RESTORED_BUILD_EXIT=0

The mutation was rejected because it changed the evaluated anchor results.
The original gcd-based implementation was restored and rebuilt successfully.

## Verification boundary

Successful builds establish reproducibility on the recorded platform.
They do not by themselves establish general mathematical correctness,
publication readiness, or C4 certification.
