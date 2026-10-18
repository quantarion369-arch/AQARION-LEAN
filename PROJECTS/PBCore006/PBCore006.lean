import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.SetNotation

/-!
# PB-CORE-006: Pullback-fixed equivalences

This module begins the Lean formalization of pullback-fixed equivalence
relations for finite endofunctions.

The current target is the permutation-core aggregate:

`S_k = k! * p(k)`

where `S_k` counts pairs consisting of a permutation of a `k`-element type
and an equivalence relation invariant under that permutation.
-/

/-- An equivalence relation `E` on `α` is invariant under a permutation
`σ` when `σ` preserves equivalence in both directions. -/
def PermutationInvariantEquiv {α : Type*}
    (σ : Equiv.Perm α) (E : α → α → Prop) : Prop :=
  ∀ x y, E x y ↔ E (σ x) (σ y)

/-- The identity permutation preserves every equivalence relation. -/
theorem permutationInvariantEquiv_refl {α : Type*}
    (E : α → α → Prop) :
    PermutationInvariantEquiv (Equiv.refl α) E := by
  intro x y
  simp [PermutationInvariantEquiv]
