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
| PBCore006 | BUILD PASS / exit 0; final job count unknown | `RECEIPTS/PBCore006-build-recovery-20261018.md` |

## PBCore006 evidence qualification

The successful `lake build` exit status 0 was observed. The saved local build log and committed placeholder receipt were empty. A captured excerpt showed 785 jobs, but the user reports the build continued beyond that excerpt. The final count is unknown; it is not reported as 785 or guessed as 1,000. The new receipt is a transparent recovered summary, not a fabricated raw log.

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

## Promotion status
- Lean formalization: OPEN
- C4: BLOCKED
- Publication: BLOCKED
- Promotion: NOT AUTHORIZED
