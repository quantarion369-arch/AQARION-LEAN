# Fresh finite-anchor verification

The anchor and join compiled successfully with Lean 4.35.0-rc4.
The join imported the freshly compiled anchor.

Four declaration reports matched:
- Finite-quotient rigidity: propext, Classical.choice, Quot.sound.
- Finite-anchor rigidity: the same standard foundations.
- Join universal property: no axioms.
- Finite-anchor join rigidity: the same standard foundations.

The reports contain no sorryAx or additional theorem-specific axiom.
This is selected-declaration formal checking, not novelty review or an
audit of every declaration. The separate Mathlib rewrite is not checked.

Receipt: evidence/finite-anchor-verify-nF7qHifJ/
Its SHA256SUMS covers the included files; compiled binaries are omitted.
Original theorem sources and historical exit records are unchanged.

Reproduce from the repository root:
    bash PROJECTS/FiniteAnchorJoinRigidity/verify.sh

Source hashes and toolchain pin only:
    bash PROJECTS/FiniteAnchorJoinRigidity/verify.sh --check-only

GitHub CI uses the same verifier. Local success is not remote CI success.
The bootstrap and action major-version tags are mutable references;
this is not hermetic supply-chain attestation.
