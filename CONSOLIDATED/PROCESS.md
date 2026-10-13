# AQARION Lean — Process Flow

## Environment chain

1. Android ARM64 hardware executes native aarch64 instructions.
2. Termux provides the Android Linux terminal environment.
3. Ubuntu proot provides the Linux userland and project root.
4. Lean 4.35.0-rc3 and Lake 5.0 run as native ARM64 ELF binaries.
5. Lake reads each project’s lean-toolchain and lake-manifest.json.
6. Lake fetches or reuses pinned dependencies, including Mathlib.
7. Lake compiles Lean sources into build artifacts.
8. Build logs, exit codes, and source hashes are written to RECEIPTS/.
9. Git commits and pushes the sources and receipts to GitHub.

## Reproduction commands

Build one project:

    cd /root/aqarion-lean-transfer/AQFPR006
    lake build

Build all projects and record receipts:

    cd /root/aqarion-lean-transfer
    ./scripts/build-all.sh

Audit verification boundaries:

    cd /root/aqarion-lean-transfer
    ./scripts/audit.sh

Create a dated project receipt:

    cd /root/aqarion-lean-transfer
    ./scripts/receipt.sh AQFPR006

## Success criterion

A full suite is successful only when it ends with:

    OVERALL_EXIT=0

and each project log contains:

    <PROJECT>_BUILD_EXIT=0
