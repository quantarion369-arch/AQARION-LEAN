# AQARION Denom5 weak-lumpability certificate (Lean 4.35.0-rc4, core only)

Example-specific, machine-checked certificate for the 3-state chain
P = (1/5)[[1,1,3],[2,2,1],[1,1,3]] with partition {0,1},{2}.
17 modules in the accepted chain; Denom5WeakLumpabilityFiniteHistory is an extra,
receipted only by a rebuild log. Axioms: propext, Classical.choice, Quot.sound
(not axiom-free). See evidence/CLAIM_SCOPE_DENOM5_v2.md for what is and is not
established. Not established: infinite-path measures, entropy-rate loss in Lean,
any general theorem, third-party reproduction. No promotion or publication
authorisation is implied.

Reproduce: install Lean 4.35.0-rc4, then run scripts/recheck_denom5.sh from a
directory containing the lean/ sources (edit the path at its top).
