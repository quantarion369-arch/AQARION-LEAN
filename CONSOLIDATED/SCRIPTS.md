# AQARION Lean — Script Reference

## scripts/build-all.sh

Rebuilds AQFPR006, PB006Audit, and PBCore006.

For each project it:

1. Creates a dated log in RECEIPTS/.
2. Runs lake build.
3. Records PROJECT_BUILD_EXIT.
4. Returns OVERALL_EXIT=0 only when every present project builds.

Usage:

    ./scripts/build-all.sh

## scripts/audit.sh

Scans Lean sources for:

- sorry
- admit
- native_decide

It also lists existing receipt files.

Usage:

    ./scripts/audit.sh

## scripts/receipt.sh

Creates a dated rebuild receipt for one project.

Usage:

    ./scripts/receipt.sh AQFPR006
    ./scripts/receipt.sh PB006Audit
    ./scripts/receipt.sh PBCore006

A receipt includes:

- Date
- Git commit
- Toolchain
- Source hashes
- Build output
- Project build exit code
