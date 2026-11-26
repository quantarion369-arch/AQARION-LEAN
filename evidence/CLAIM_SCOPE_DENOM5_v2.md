# DENOM5 CLAIM SCOPE v2

## Established (machine-checked, Lean 4.35.0-rc4, aarch64, core Lean only, no Mathlib)
All 17 listed modules build from source in dependency order, with exit code 0,
no sorry and no sorryAx, and the rebuilt objects are byte-identical to the
originals on the same machine. Reported axioms: propext, Classical.choice,
Quot.sound. The development is NOT axiom-free.

For the 3-state chain P = (1/5)[[1,1,3],[2,2,1],[1,1,3]] with partition {0,1},{2}:
- rational invariant-plane and span structure, observation intertwining;
- a stochastic lift L(s,t) = (s/2, s/2, t) with exact intertwining on balanced vectors;
- for every balanced rational start, hidden filtered masses equal observed masses
  for every finite history, and obey the 3/5, 2/5, 2/5, 3/5 rule after every history;
- for nonnegative starts with positive mass, equal A-to-A ratios at times 0 and 1
  hold if and only if the start is balanced (a = b);
- the probability-vector parametrisation of balanced starts (t, t, 1-2t), 0 <= t <= 1/2.
These are cross-multiplied mass identities on filtered vectors.

## Not established
- Any measure on infinite paths (no probability space is constructed in Lean).
- The full homogeneous Markov property over all histories for unbalanced starts
  (only a two-step necessity test is formalised).
- Entropy-rate loss: the closed form (3/20)log2(3) + 1/5 bits (about 0.437744) is a
  hand calculation, not a Lean theorem.
- A general Gurvits-Ledoux or Pitman-Rogers theorem.
- Independent reproduction by a third party.
- Any promotion, publication or ClaimLock status.

## Provenance caveats
- Several mass identities are definitional (rfl); a Core2 uniqueness theorem has
  unused hypotheses. They are bookkeeping, not discoveries.
- This is an example-specific certificate of classical theory (Burke-Rosenblatt 1958,
  Rogers-Pitman, Rubino-Sericola, Ledoux, Geiger-Temmel). Verify each reference
  against the publisher record before citing.
- Failed attempts exist in the project directory and are listed as NOT_ACCEPTED
  in the manifest; they are not evidence.

## Reproduce
Run recheck_denom5.sh from the project directory with the pinned Lean binary.
