import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Aqarion.P2Facets

def form : Nat → Int → Int → Int → Int → Int → Int
  | 0, a0, _, _, _, _ => a0
  | 1, _, a1, _, _, _ => a1
  | 2, _, _, a2, _, _ => a2
  | 3, _, _, _, a3, _ => a3
  | 4, a0, a1, _, _, k => a0 + a1 - k
  | 5, a0, _, a2, _, k => a0 + a2 - k
  | 6, a0, _, _, a3, k => a0 + a3 - k
  | 7, _, a1, a2, _, k => a1 + a2 - k
  | 8, _, a1, _, a3, k => a1 + a3 - k
  | 9, _, _, a2, a3, k => a2 + a3 - k
  | _, _, _, _, _, _ => 0

def formT (i : Nat) (w : Int × Int × Int × Int × Int) : Int :=
  form i w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2

def witness : Nat → Int × Int × Int × Int × Int
  | 0 => (0, 2, 2, 2, 1)
  | 1 => (2, 0, 2, 2, 1)
  | 2 => (2, 2, 0, 2, 1)
  | 3 => (2, 2, 2, 0, 1)
  | 4 => (1, 1, 2, 2, 2)
  | 5 => (1, 2, 1, 2, 2)
  | 6 => (1, 2, 2, 1, 2)
  | 7 => (2, 1, 1, 2, 2)
  | 8 => (2, 1, 2, 1, 2)
  | 9 => (2, 2, 1, 1, 2)
  | _ => (0, 0, 0, 0, 0)

theorem facets_irredundant :
    ∀ i, i < 10 → formT i (witness i) = 0 ∧
      ∀ j, j < 10 → j ≠ i → 0 < formT j (witness i) := by
  decide

theorem interior_witness :
    ∀ j, j < 10 → 0 < formT j ((1, 1, 1, 1, 1) : Int × Int × Int × Int × Int) := by
  decide

theorem lattice_spanned (a0 a1 a2 a3 k : Int) :
    ∃ cA c0 c1 c2 c3 : Int,
      a0 = 0 * cA + 1 * c0 + 0 * c1 + 0 * c2 + 0 * c3 ∧
      a1 = 0 * cA + 0 * c0 + 1 * c1 + 0 * c2 + 0 * c3 ∧
      a2 = 0 * cA + 0 * c0 + 0 * c1 + 1 * c2 + 0 * c3 ∧
      a3 = 0 * cA + 0 * c0 + 0 * c1 + 0 * c2 + 1 * c3 ∧
      k = (-1) * cA + 0 * c0 + 0 * c1 + 0 * c2 + 0 * c3 := by
  refine ⟨-k, a0, a1, a2, a3, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Aqarion.P2Facets

#print axioms Aqarion.P2Facets.facets_irredundant
#print axioms Aqarion.P2Facets.interior_witness
#print axioms Aqarion.P2Facets.lattice_spanned
