# AQARION Lean Transfer

This repository contains current transferable Lean sources and on-device
build receipts for the AQARION Lean work.

## Contents

- AQFPR006/ — repaired weighted-Bell / restricted-growth-string artifact.
- PB006Audit/ — Lean audit and benchmark artifact.
- PBCore006/ — source transferred for future build verification.
- RECEIPTS/ — build and semantic-mutation receipts.

## Platform

The recorded builds were performed on Android using Termux and Ubuntu proot,
with native ARM64 Linux ELF Lean binaries.

## Reproduce

Each Lean project contains its own lakefile and lean-toolchain.
From within a project directory:

    lake build

Dependencies are resolved through the checked-in lake-manifest.json.
Build artifacts and package caches are not committed.

## Status

See STATUS.md.
