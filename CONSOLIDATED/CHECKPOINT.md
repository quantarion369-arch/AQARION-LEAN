# AQARION Lean — Consolidated Checkpoint

Checkpoint date: 2026-10-13  
Authoritative repository: AQARION-LEAN-TRANSFER  
Base synced commit: 19311e0  
Local working copy: /root/aqarion-lean-transfer

## Platform

- Host: Android / Termux
- Container: Ubuntu proot
- Architecture: ARM64 / aarch64
- Binary format: native Linux ELF
- Lean: 4.35.0-rc3
- Lake: 5.0.0
- Execution model: native ARM64 execution under proot, not CPU emulation

## Build ledger

| Project | Status | Evidence |
|---|---|---|
| AQFPR006 | REBUILT / REPRODUCED / GATE 2 PASSED | RECEIPTS/AQFPR006-20261013T045626Z.log |
| PB006Audit | REBUILT / REPRODUCED | RECEIPTS/PB006Audit-20261013T045626Z.log |
| PBCore006 | REBUILT / REPRODUCED | RECEIPTS/PBCore006-20261013T045626Z.log |
| Full suite | PASSED | OVERALL_EXIT=0 |

## Verification boundary

A successful Lean build establishes that the pinned source revision compiles in the recorded environment.

It does not establish:

- A completed general mathematical proof
- C4 certification
- Publication readiness
- Promotion authorization
- Independent external reproduction

## Current claims

- AQFPR006 contains repaired weighted-Bell and restricted-growth-string logic.
- AQFPR006 passes the recorded finite anchors.
- Gate 2 detects the tested listGcd-to-lcm mutation.
- PB006Audit and PBCore006 compile from their transferred revisions.
- PB-CORE-006’s EGF should use P(T(z)), not P(T(z)) - 1.
- The coefficient semantics of PBCore006 remain open.

## Promotion status

- Lean formalization: OPEN
- C4: BLOCKED
- Publication: BLOCKED
- Promotion: NOT AUTHORIZED
