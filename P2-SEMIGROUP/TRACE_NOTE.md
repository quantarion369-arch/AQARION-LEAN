# Unit-pivot trace: formal scope and wording erratum

Date: 2026-11-24. Additive note; historical receipts and evidence bundles are unchanged.

## What is formalized

`P2Mathlib.rank_of_unitTrace` (file `p2-mathlib/P2Mathlib/UnitTrace.lean`) is built and gated in CI
(see `CI_RECEIPT_CURRENT.json`). A `UnitTrace` of length `r` on an integer matrix is a sequence of
steps. Each step picks an entry equal to 1 or -1, removes that row and column, and replaces every
remaining entry `M a b` by `M a b - M a j * M i j * M i b`. The trace is valid when the final matrix
is zero. The theorem states that such a matrix has rank exactly `r` over every field. See the source
for the exact statement.

The Lean proof uses only a row-space dimension argument: the pivot row is independent of the
reduced rows because only the pivot row is nonzero in the pivot column. It performs no column
operations.

## Match with the original verifier

The saved traces come from `reduce_units` in the integral evidence `verify.py` (AQARION evidence
commit 139dd97, lines 197-242). That routine is row-only: it chooses any entry of absolute value 1,
removes that row as the pivot row, and subtracts `row[j] * unit` times the pivot row from every
remaining row containing column `j`. A trace is valid when no rows remain. This is the same update
as the Schur step above, because a pivot of plus or minus 1 is its own inverse.

## Wording erratum

Two statements over-describe the original routine:

- the verifier's printed claim "integral Smith form I_r plus zero" (verify.py line 317);
- the proof-boundary wording "unimodular row/column operations".

The routine performs row operations only and does not output Smith transformation matrices. The
conclusions drawn from the trace remain correct, by the following argument, which is a mathematical
remark and is NOT formalized in Lean: the retained pivot rows, restricted to the pivot columns in
trace order, form a triangular matrix with diagonal entries plus or minus 1, so an r-by-r minor is a
unit; the zero residual rows bound the rank above by r. Since row operations are unimodular, the
ideal of r-by-r minors is the unit ideal, so the product of the nonzero Smith invariant factors is 1
and each of them is 1. The second implementation's column-only replay is a separate corroborating
route to the same determinantal-ideal conclusion. It is a second implementation, not an independent
external reproduction.

## Not claimed

The generic theorem does not show that the nine frozen component matrices, their monomial ordering
and the saved JSON triples are instances of `UnitTrace`; that binding is open. Lemma 2, kernel
generation and the overall resolution theorem remain `DRAFT_REQUIRING_REVIEW`.
