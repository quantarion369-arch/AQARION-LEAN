import Mathlib
import P2Bridge.Cone

set_option autoImplicit false

namespace Aqarion.P2Cone

/-- Generator vectors in (a0, a1, a2, a3, k) coordinates. -/
def vA : Fin 5 → ℝ := ![0, 0, 0, 0, -1]
def vE0 : Fin 5 → ℝ := ![1, 0, 0, 0, 0]
def vE1 : Fin 5 → ℝ := ![0, 1, 0, 0, 0]
def vE2 : Fin 5 → ℝ := ![0, 0, 1, 0, 0]
def vE3 : Fin 5 → ℝ := ![0, 0, 0, 1, 0]
def vB0 : Fin 5 → ℝ := ![0, 1, 1, 1, 1]
def vB1 : Fin 5 → ℝ := ![1, 0, 1, 1, 1]
def vB2 : Fin 5 → ℝ := ![1, 1, 0, 1, 1]
def vB3 : Fin 5 → ℝ := ![1, 1, 1, 0, 1]
def vC : Fin 5 → ℝ := ![1, 1, 1, 1, 2]

/-- Nonnegative real combinations of the ten generators. -/
def genCone : Set (Fin 5 → ℝ) :=
  {x | ∃ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℝ,
    0 ≤ c0 ∧ 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 ∧ 0 ≤ c4 ∧
    0 ≤ c5 ∧ 0 ≤ c6 ∧ 0 ≤ c7 ∧ 0 ≤ c8 ∧ 0 ≤ c9 ∧
    x = c0 • vA + c1 • vE0 + c2 • vE1 + c3 • vE2 + c4 • vE3 +
        c5 • vB0 + c6 • vB1 + c7 • vB2 + c8 • vB3 + c9 • vC}

theorem genCone_subset_cone : genCone ⊆ cone := by
  rintro x ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩ j
  fin_cases j <;> simp [facet, vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> linarith

theorem cone_subset_genCone : cone ⊆ genCone := by
  intro x hx
  have f0 : 0 ≤ x 0 := by simpa [facet] using hx 0
  have f1 : 0 ≤ x 1 := by simpa [facet] using hx 1
  have f2 : 0 ≤ x 2 := by simpa [facet] using hx 2
  have f3 : 0 ≤ x 3 := by simpa [facet] using hx 3
  have p01 : x 4 ≤ x 0 + x 1 := by simpa [facet] using hx 4
  have p02 : x 4 ≤ x 0 + x 2 := by simpa [facet] using hx 5
  have p03 : x 4 ≤ x 0 + x 3 := by simpa [facet] using hx 6
  have p12 : x 4 ≤ x 1 + x 2 := by simpa [facet] using hx 7
  have p13 : x 4 ≤ x 1 + x 3 := by simpa [facet] using hx 8
  have p23 : x 4 ≤ x 2 + x 3 := by simpa [facet] using hx 9
  by_cases hk : x 4 ≤ 0
  · refine ⟨-x 4, x 0, x 1, x 2, x 3, 0, 0, 0, 0, 0, by linarith, f0, f1, f2, f3,
      le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, ?_⟩
    funext m
    fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring
  · push_neg at hk
    by_cases h0 : 2 * x 0 < x 4
    · refine ⟨0, 0, x 1 - (x 4 - x 0), x 2 - (x 4 - x 0), x 3 - (x 4 - x 0),
        x 4 - 2 * x 0, 0, 0, 0, x 0,
        le_refl _, le_refl _, by linarith, by linarith, by linarith, by linarith,
        le_refl _, le_refl _, le_refl _, f0, ?_⟩
      funext m
      fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring
    · push_neg at h0
      by_cases h1 : 2 * x 1 < x 4
      · refine ⟨0, x 0 - (x 4 - x 1), 0, x 2 - (x 4 - x 1), x 3 - (x 4 - x 1),
          0, x 4 - 2 * x 1, 0, 0, x 1,
          le_refl _, by linarith, le_refl _, by linarith, by linarith,
          le_refl _, by linarith, le_refl _, le_refl _, f1, ?_⟩
        funext m
        fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring
      · push_neg at h1
        by_cases h2 : 2 * x 2 < x 4
        · refine ⟨0, x 0 - (x 4 - x 2), x 1 - (x 4 - x 2), 0, x 3 - (x 4 - x 2),
            0, 0, x 4 - 2 * x 2, 0, x 2,
            le_refl _, by linarith, by linarith, le_refl _, by linarith,
            le_refl _, le_refl _, by linarith, le_refl _, f2, ?_⟩
          funext m
          fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring
        · push_neg at h2
          by_cases h3 : 2 * x 3 < x 4
          · refine ⟨0, x 0 - (x 4 - x 3), x 1 - (x 4 - x 3), x 2 - (x 4 - x 3), 0,
              0, 0, 0, x 4 - 2 * x 3, x 3,
              le_refl _, by linarith, by linarith, by linarith, le_refl _,
              le_refl _, le_refl _, le_refl _, by linarith, f3, ?_⟩
            funext m
            fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring
          · push_neg at h3
            refine ⟨0, x 0 - x 4 / 2, x 1 - x 4 / 2, x 2 - x 4 / 2, x 3 - x 4 / 2,
              0, 0, 0, 0, x 4 / 2,
              le_refl _, by linarith, by linarith, by linarith, by linarith,
              le_refl _, le_refl _, le_refl _, le_refl _, by linarith, ?_⟩
            funext m
            fin_cases m <;> simp [vA, vE0, vE1, vE2, vE3, vB0, vB1, vB2, vB3, vC] <;> ring

theorem cone_eq_genCone : cone = genCone :=
  Set.Subset.antisymm cone_subset_genCone genCone_subset_cone

end Aqarion.P2Cone

#print axioms Aqarion.P2Cone.cone_eq_genCone
