# AQARION LEAN

This repository contains the current transferable Lean sources, on-device Android ARM64 build receipts, and consolidated checkpoint documentation for the AQARION Lean work.

## Contents

- AQFPR006/ — repaired weighted-Bell / restricted-growth-string artifact.
- PB006Audit/ — Lean audit and benchmark artifact.
- PBCore006/ — source transferred for build verification and mathematical review.
- RECEIPTS/ — build logs, hashes, exit codes, and verification receipts.
- scripts/ — build, audit, and receipt helper scripts.
- CONSOLIDATED/ — single entry point for the current checkpoint, process, evidence, examples, and script reference.

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
