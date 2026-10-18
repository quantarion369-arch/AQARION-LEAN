# AQARION Lean — Consolidated Checkpoint

Checkpoint updated: 2026-10-18
Canonical repository: https://github.com/quantarion369-arch/AQARION-LEAN
Local working copy: `/root/aqarion-lean-transfer`

## Platform
- Host: Android / Termux
- Container: Ubuntu proot
- Architecture: ARM64 / aarch64
- Binary format: native Linux ELF
- Lean: 4.35.0-rc3
- Lake: 5.0.0
- Execution: native ARM64 under proot, not CPU emulation

## Build ledger

| Project | Status | Evidence |
|---|---|---|
| AQFPR006 | REBUILT / REPRODUCED / GATE 2 PASSED | Existing AQFPR006 receipts |
| PB006Audit | REBUILT / REPRODUCED | Existing PB006Audit receipt |
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


## Verification boundary

A successful Lean build establishes that the compiled source was accepted in the recorded environment. It does not establish:
- A completed general mathematical proof
- C4 certification
- Publication readiness
- Promotion authorization
- Independent external reproduction

## Current claims and limits
- AQFPR006 contains repaired weighted-Bell and restricted-growth-string logic.
- AQFPR006 passes its recorded finite anchors.
- Gate 2 detects the tested listGcd-to-lcm mutation.
- PB006Audit and PBCore006 have successful build evidence.
- PB-CORE-006’s EGF should use P(T(z)), not P(T(z)) - 1.
- The coefficient semantics of PBCore006 remain open.

## Project decisions

PBCore006 build: PASS.

This build record does not assign C4, publication, or promotion status.
The previous blanket labels are withdrawn from this report; any such decision requires its own stated criteria.
