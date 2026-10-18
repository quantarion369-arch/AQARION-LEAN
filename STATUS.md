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
| PBCore006 | BUILD PASS / 785 jobs / LAKE_EXIT=0 / LOG_EXIT=0 | RECEIPTS/PBCore006-build-result-20261017.md |

## PBCore006 — Successful Build Record

BUILD PASS.

Command: lake build
Environment: Termux / Ubuntu proot / ARM64
Resume: 2026-10-17T22:15:00-04:00

Build completed successfully (785 jobs).
LAKE_EXIT=0
LOG_EXIT=0
BUILD FINISHED SUCCESSFULLY

The displayed warnings were non-fatal. No build recovery was required.

Console log: PBCore006-20261017-console.log
SHA-256: 0ef92b13e35a1785831ede359280b373f8f2dd9043f8e77afd43aa1616d824a1


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

## Project decisions

PBCore006 build: PASS.

This build record does not assign C4, publication, or promotion status.
The previous blanket labels are withdrawn from this report; any such decision requires its own stated criteria.
