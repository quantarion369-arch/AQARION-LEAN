# Temporal observability checkpoint — 2026-10-29

## Contents

- saved-local-artifacts/: copies of existing six-cycle certificate,
  checkpoint, rank-module, and finite-bridge text artifacts found on-device.
- SHA256SUMS: SHA-256 hashes of those copied local artifacts.
- horizon-degree-frontier.csv: transcription of the exact 12-cycle
  calculation performed in the accompanying chat, not rerun by this
  publication script.

## Twelve-cycle computational result

Word: 000000101101.
Transition: T(i) = (i + 1) mod 12.
Observation: f_t(i) = h[(i + t) mod 12].
Matrix orientation: states are rows, features are columns.

Ordered basis:
1, f0, f1, f2, f3, f4, f5,
f0*f1, f0*f2, f0*f3, f1*f2, f1*f3.

The chat calculation returned determinant -1 for this ordered basis.
It returned minimum consecutive horizon 6 and minimum degree 2 at
that horizon. States 0 and 1 have the same first-five history, 00000.

## Verification boundary

This is a research/source checkpoint, not a new Lean build receipt.
The publication script did not run Lean or revalidate copied receipts.
Copied files may contain failed attempts and superseded revisions.
Their presence does not confer PASS status.

No source-to-artifact correspondence theorem, general JSON acceptance
theorem, or infinite-span Lean formalization is claimed here.
Nothing in this folder is wired into the existing project builds.
