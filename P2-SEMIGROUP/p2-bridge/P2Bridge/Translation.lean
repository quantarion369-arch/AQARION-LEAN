import Mathlib
import P2Bridge.Closure
import P2Bridge.Cone

set_option autoImplicit false

namespace Aqarion.P2Bridge

open Aqarion.P2Cone

/-- An integer degree vector viewed as a real point. -/
def realPoint (a0 a1 a2 a3 k : ℤ) : Fin 5 → ℝ :=
  ![(a0 : ℝ), (a1 : ℝ), (a2 : ℝ), (a3 : ℝ), (k : ℝ)]

theorem realPoint_mem_strictCone_iff {a0 a1 a2 a3 k : ℤ} :
    realPoint a0 a1 a2 a3 k ∈ strictCone ↔
      Aqarion.P2Arithmetic.StrictFeasible a0 a1 a2 a3 k := by
  constructor
  · intro hx
    have r0 : (0 : ℝ) < a0 := by simpa [facet, realPoint] using hx 0
    have r1 : (0 : ℝ) < a1 := by simpa [facet, realPoint] using hx 1
    have r2 : (0 : ℝ) < a2 := by simpa [facet, realPoint] using hx 2
    have r3 : (0 : ℝ) < a3 := by simpa [facet, realPoint] using hx 3
    have r4 : (k : ℝ) < a0 + a1 := by simpa [facet, realPoint] using hx 4
    have r5 : (k : ℝ) < a0 + a2 := by simpa [facet, realPoint] using hx 5
    have r6 : (k : ℝ) < a0 + a3 := by simpa [facet, realPoint] using hx 6
    have r7 : (k : ℝ) < a1 + a2 := by simpa [facet, realPoint] using hx 7
    have r8 : (k : ℝ) < a1 + a3 := by simpa [facet, realPoint] using hx 8
    have r9 : (k : ℝ) < a2 + a3 := by simpa [facet, realPoint] using hx 9
    have i0 : 0 < a0 := by exact_mod_cast r0
    have i1 : 0 < a1 := by exact_mod_cast r1
    have i2 : 0 < a2 := by exact_mod_cast r2
    have i3 : 0 < a3 := by exact_mod_cast r3
    have i4 : k < a0 + a1 := by exact_mod_cast r4
    have i5 : k < a0 + a2 := by exact_mod_cast r5
    have i6 : k < a0 + a3 := by exact_mod_cast r6
    have i7 : k < a1 + a2 := by exact_mod_cast r7
    have i8 : k < a1 + a3 := by exact_mod_cast r8
    have i9 : k < a2 + a3 := by exact_mod_cast r9
    constructor <;> omega
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    have i0 : 0 < a0 := by omega
    have i1 : 0 < a1 := by omega
    have i2 : 0 < a2 := by omega
    have i3 : 0 < a3 := by omega
    have i4 : k < a0 + a1 := by omega
    have i5 : k < a0 + a2 := by omega
    have i6 : k < a0 + a3 := by omega
    have i7 : k < a1 + a2 := by omega
    have i8 : k < a1 + a3 := by omega
    have i9 : k < a2 + a3 := by omega
    have r0 : (0 : ℝ) < a0 := by exact_mod_cast i0
    have r1 : (0 : ℝ) < a1 := by exact_mod_cast i1
    have r2 : (0 : ℝ) < a2 := by exact_mod_cast i2
    have r3 : (0 : ℝ) < a3 := by exact_mod_cast i3
    have r4 : (k : ℝ) < a0 + a1 := by exact_mod_cast i4
    have r5 : (k : ℝ) < a0 + a2 := by exact_mod_cast i5
    have r6 : (k : ℝ) < a0 + a3 := by exact_mod_cast i6
    have r7 : (k : ℝ) < a1 + a2 := by exact_mod_cast i7
    have r8 : (k : ℝ) < a1 + a3 := by exact_mod_cast i8
    have r9 : (k : ℝ) < a2 + a3 := by exact_mod_cast i9
    intro j
    fin_cases j <;> simp [facet, realPoint] <;> linarith

theorem realPoint_mem_cone_iff {a0 a1 a2 a3 k : ℤ} :
    realPoint a0 a1 a2 a3 k ∈ cone ↔ Aqarion.P2Gen.Feasible a0 a1 a2 a3 k := by
  constructor
  · intro hx
    have r0 : (0 : ℝ) ≤ a0 := by simpa [facet, realPoint] using hx 0
    have r1 : (0 : ℝ) ≤ a1 := by simpa [facet, realPoint] using hx 1
    have r2 : (0 : ℝ) ≤ a2 := by simpa [facet, realPoint] using hx 2
    have r3 : (0 : ℝ) ≤ a3 := by simpa [facet, realPoint] using hx 3
    have r4 : (k : ℝ) ≤ a0 + a1 := by simpa [facet, realPoint] using hx 4
    have r5 : (k : ℝ) ≤ a0 + a2 := by simpa [facet, realPoint] using hx 5
    have r6 : (k : ℝ) ≤ a0 + a3 := by simpa [facet, realPoint] using hx 6
    have r7 : (k : ℝ) ≤ a1 + a2 := by simpa [facet, realPoint] using hx 7
    have r8 : (k : ℝ) ≤ a1 + a3 := by simpa [facet, realPoint] using hx 8
    have r9 : (k : ℝ) ≤ a2 + a3 := by simpa [facet, realPoint] using hx 9
    have i0 : 0 ≤ a0 := by exact_mod_cast r0
    have i1 : 0 ≤ a1 := by exact_mod_cast r1
    have i2 : 0 ≤ a2 := by exact_mod_cast r2
    have i3 : 0 ≤ a3 := by exact_mod_cast r3
    have i4 : k ≤ a0 + a1 := by exact_mod_cast r4
    have i5 : k ≤ a0 + a2 := by exact_mod_cast r5
    have i6 : k ≤ a0 + a3 := by exact_mod_cast r6
    have i7 : k ≤ a1 + a2 := by exact_mod_cast r7
    have i8 : k ≤ a1 + a3 := by exact_mod_cast r8
    have i9 : k ≤ a2 + a3 := by exact_mod_cast r9
    constructor <;> omega
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    have i0 : 0 ≤ a0 := by omega
    have i1 : 0 ≤ a1 := by omega
    have i2 : 0 ≤ a2 := by omega
    have i3 : 0 ≤ a3 := by omega
    have i4 : k ≤ a0 + a1 := by omega
    have i5 : k ≤ a0 + a2 := by omega
    have i6 : k ≤ a0 + a3 := by omega
    have i7 : k ≤ a1 + a2 := by omega
    have i8 : k ≤ a1 + a3 := by omega
    have i9 : k ≤ a2 + a3 := by omega
    have r0 : (0 : ℝ) ≤ a0 := by exact_mod_cast i0
    have r1 : (0 : ℝ) ≤ a1 := by exact_mod_cast i1
    have r2 : (0 : ℝ) ≤ a2 := by exact_mod_cast i2
    have r3 : (0 : ℝ) ≤ a3 := by exact_mod_cast i3
    have r4 : (k : ℝ) ≤ a0 + a1 := by exact_mod_cast i4
    have r5 : (k : ℝ) ≤ a0 + a2 := by exact_mod_cast i5
    have r6 : (k : ℝ) ≤ a0 + a3 := by exact_mod_cast i6
    have r7 : (k : ℝ) ≤ a1 + a2 := by exact_mod_cast i7
    have r8 : (k : ℝ) ≤ a1 + a3 := by exact_mod_cast i8
    have r9 : (k : ℝ) ≤ a2 + a3 := by exact_mod_cast i9
    intro j
    fin_cases j <;> simp [facet, realPoint] <;> linarith

/-- Integer points of the real cone are exactly the semigroup generated by the ten generators. -/
theorem realPoint_mem_cone_iff_closure {a0 a1 a2 a3 k : ℤ} :
    realPoint a0 a1 a2 a3 k ∈ cone ↔ v5 a0 a1 a2 a3 k ∈ genClosure := by
  rw [realPoint_mem_cone_iff]
  exact mem_closure_iff_feasible.symm

/-- Interior integer points are the translate by kappa = (1,1,1,1,1) of the semigroup. -/
theorem interior_realPoint_iff {a0 a1 a2 a3 k : ℤ} :
    realPoint a0 a1 a2 a3 k ∈ interior cone ↔
      v5 (a0 - 1) (a1 - 1) (a2 - 1) (a3 - 1) (k - 1) ∈ genClosure := by
  rw [interior_cone, realPoint_mem_strictCone_iff]
  exact strict_iff_closure_shift

end Aqarion.P2Bridge

#print axioms Aqarion.P2Bridge.realPoint_mem_strictCone_iff
#print axioms Aqarion.P2Bridge.realPoint_mem_cone_iff_closure
#print axioms Aqarion.P2Bridge.interior_realPoint_iff
