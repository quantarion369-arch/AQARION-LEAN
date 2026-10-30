# AQARION LEAN

<!-- PBCORE006-BUILD-PASS-20261017 -->
## PBCore006 — Successful Lean Build

PBCore006 completed `lake build` successfully in Termux / Ubuntu proot on ARM64.

```text
Build completed successfully (785 jobs).
LAKE_EXIT=0
LOG_EXIT=0
BUILD FINISHED SUCCESSFULLY
```

- Resume timestamp: `2026-10-17T22:15:00-04:00`.
- The displayed warnings were non-fatal.
- [Successful build record](RECEIPTS/PBCore006-build-result-20261017.md)
- [Actual console log](RECEIPTS/PBCore006-20261017-console.log)

The console log was copied from the device log with matching SHA-256:

`0ef92b13e35a1785831ede359280b373f8f2dd9043f8e77afd43aa1616d824a1`



This repository contains the current transferable Lean sources, on-device Android ARM64 build receipts, and consolidated checkpoint documentation for the AQARION Lean work.

## Contents

- AQFPR006/ — repaired weighted-Bell / restricted-growth-string artifact.
- PB006Audit/ — Lean audit and benchmark artifact.
- PBCore006/ — Lean project source and build artifacts; see the successful build receipt above. Mathematical review remains a separate obligation.
- RECEIPTS/ — build logs, hashes, exit codes, and verification receipts.
- scripts/ — build, audit, and receipt helper scripts.
- CONSOLIDATED/ — single entry point for the current checkpoint, process, evidence, examples, and script reference.

## AQARION Project Ecosystem

This repository is the Lean formalization and build-verification component of the broader AQARION project.

- **[AQARION-LEAN](https://github.com/quantarion369-arch/AQARION-LEAN)** — Lean sources, formal verification, and build receipts.
- **[AQARION](https://github.com/quantarion369-arch/AQARION)** — research artifacts, computational evidence, and provenance.
- **[Aqarion-Fastapi](https://github.com/quantarion369-arch/Aqarion-Fastapi)** — API and operational integration.

These repositories have distinct responsibilities. A successful Lean build establishes compilation success for the built targets; it does not, by itself, establish every mathematical claim, validate all computational evidence, or certify publication readiness.

## Start here

Open:

    CONSOLIDATED/CHECKPOINT.md

That file contains the current build ledger, verification boundary, and promotion status.

## Platform

The recorded builds were performed on Android using Termux and Ubuntu proot, with native ARM64 Linux ELF Lean binaries.

- Lean: 4.35.0-rc3
- Lake: 5.0.0
- Architecture: aarch64 / ARM64
- Execution: native ELF under proot, not CPU emulation

## Reproduce

Each Lean project contains its own lakefile and lean-toolchain. From within a project directory:

    lake build

To rebuild all projects and record receipts:

    ./scripts/build-all.sh

To inspect proof and computational-check boundaries:

    ./scripts/audit.sh

## Status

See CONSOLIDATED/CHECKPOINT.md and STATUS.md.

AQFPR006, PB006Audit, and PBCore006 have fresh successful builds in the recorded environment. Mathematical formalization, C4 certification, publication readiness, and promotion remain separate open obligations.
