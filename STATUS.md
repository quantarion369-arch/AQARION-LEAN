# AQARION Lean Build Status

## Platform
- Android / Termux
- Ubuntu proot
- ARM64/aarch64 native Linux ELF Lean binaries
- Lean 4.35.0-rc3
- Lake 5.0.0

## Build ledger

| Project | Status | Evidence |
|---|---|---|
| AQFPR006 | REBUILT / BASELINE GREEN / GATE 2 PASS | Existing AQFPR006 and Gate 2 receipts |
| PB006Audit | REBUILT / BASELINE GREEN | Existing PB006Audit build receipt |
| PBCore006 | BUILD PASS / exit 0; final job count not recovered | RECEIPTS/PBCore006-build-recovery-20261018.md |

## PBCore006 build record

A successful `lake build` was observed in the Android/Termux Ubuntu-proot ARM64 environment using Lean 4.35.0-rc3 and Lake 5.0.0. The command exited with status 0.

The saved build log and its originally committed receipt were both zero bytes. An earlier captured excerpt showed 785 jobs, but that was not the end of the run. The user reports the build continued beyond that point. The exact final job count is not recoverable from the surviving files; 785 is not asserted as the final total, and no estimate is presented as fact.

See `RECEIPTS/PBCore006-build-recovery-20261018.md` for the evidence boundary. No rebuild is required for this documentation correction.

## AQFPR006 repair
- Replaced unavailable List.get! indexing with current bounded list indexing.
- Repaired rgs so an empty restricted-growth-string prefix emits only label 0.
- Verified partitions 3 produces exactly five set-partition structures.
- Recorded anchors: weightedBell [1,1,2] = 7, [2,2] = 7, [2,2,2] = 31, [2,4] = 9, [3,3] = 8.

## Gate 2
- BASELINE_BUILD_EXIT=0
- MUTATION_BUILD_EXIT=1
- RESTORED_BUILD_EXIT=0

The tested gcd-to-lcm mutation changed evaluated anchor results and was rejected. The original gcd implementation was restored and rebuilt.

## Verification boundary
Successful builds establish compilation in the recorded environment. They do not by themselves establish general mathematical correctness, publication readiness, or C4 certification.

## Promotion status
- Lean formalization: OPEN
- C4: BLOCKED
- Publication: BLOCKED
- Promotion: NOT AUTHORIZED
