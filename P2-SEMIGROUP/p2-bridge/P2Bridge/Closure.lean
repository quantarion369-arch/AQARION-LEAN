import Mathlib
import ArithmeticKernel
import GenKernel

set_option autoImplicit false

namespace Aqarion.P2Bridge

/-- Degree vector (a0, a1, a2, a3, k). -/
def v5 (a0 a1 a2 a3 k : ℤ) : Fin 5 → ℤ := ![a0, a1, a2, a3, k]

/-- The ten generator degrees A, E0-E3, B0-B3, C. -/
def genDegrees : Set (Fin 5 → ℤ) :=
  {v5 0 0 0 0 (-1), v5 1 0 0 0 0, v5 0 1 0 0 0, v5 0 0 1 0 0, v5 0 0 0 1 0,
   v5 0 1 1 1 1, v5 1 0 1 1 1, v5 1 1 0 1 1, v5 1 1 1 0 1, v5 1 1 1 1 2}

abbrev genClosure : AddSubmonoid (Fin 5 → ℤ) := AddSubmonoid.closure genDegrees

theorem v5_add {a0 a1 a2 a3 k b0 b1 b2 b3 l : ℤ} :
    v5 a0 a1 a2 a3 k + v5 b0 b1 b2 b3 l =
      v5 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (k + l) := by
  funext i
  fin_cases i <;> simp [v5]

theorem v5_zero : v5 0 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> simp [v5]

/-- Additive submonoid of feasible degree vectors. -/
def feasSub : AddSubmonoid (Fin 5 → ℤ) where
  carrier := {x | Aqarion.P2Gen.Feasible (x 0) (x 1) (x 2) (x 3) (x 4)}
  zero_mem' := by
    show Aqarion.P2Gen.Feasible 0 0 0 0 0
    constructor <;> omega
  add_mem' := by
    intro x y hx hy
    obtain ⟨a0, a1, a2, a3, a01, a02, a03, a12, a13, a23⟩ := hx
    obtain ⟨b0, b1, b2, b3, b01, b02, b03, b12, b13, b23⟩ := hy
    show Aqarion.P2Gen.Feasible (x 0 + y 0) (x 1 + y 1) (x 2 + y 2) (x 3 + y 3) (x 4 + y 4)
    constructor <;> omega

theorem v5_mem_feasSub {a0 a1 a2 a3 k : ℤ} (h : Aqarion.P2Gen.Feasible a0 a1 a2 a3 k) :
    v5 a0 a1 a2 a3 k ∈ feasSub := by
  show Aqarion.P2Gen.Feasible (v5 a0 a1 a2 a3 k 0) (v5 a0 a1 a2 a3 k 1)
    (v5 a0 a1 a2 a3 k 2) (v5 a0 a1 a2 a3 k 3) (v5 a0 a1 a2 a3 k 4)
  simpa [v5] using h

theorem closure_le_feasSub : genClosure ≤ feasSub := by
  apply AddSubmonoid.closure_le.2
  intro x hx
  simp only [genDegrees, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)
  · exact v5_mem_feasSub (by constructor <;> omega)

theorem step {a0 a1 a2 a3 k b0 b1 b2 b3 l c0 c1 c2 c3 m : ℤ}
    (hx : v5 a0 a1 a2 a3 k ∈ genClosure) (hg : v5 b0 b1 b2 b3 l ∈ genClosure)
    (e0 : c0 = a0 + b0) (e1 : c1 = a1 + b1) (e2 : c2 = a2 + b2)
    (e3 : c3 = a3 + b3) (e : m = k + l) :
    v5 c0 c1 c2 c3 m ∈ genClosure := by
  subst e0 e1 e2 e3 e
  rw [← v5_add]
  exact AddSubmonoid.add_mem _ hx hg

theorem gA_mem : v5 0 0 0 0 (-1) ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gE0_mem : v5 1 0 0 0 0 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gE1_mem : v5 0 1 0 0 0 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gE2_mem : v5 0 0 1 0 0 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gE3_mem : v5 0 0 0 1 0 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gB0_mem : v5 0 1 1 1 1 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gB1_mem : v5 1 0 1 1 1 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gB2_mem : v5 1 1 0 1 1 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gB3_mem : v5 1 1 1 0 1 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])
theorem gC_mem : v5 1 1 1 1 2 ∈ genClosure :=
  AddSubmonoid.subset_closure (by simp [genDegrees])

theorem gen_mem_closure {a0 a1 a2 a3 k : ℤ} (h : Aqarion.P2Gen.Gen a0 a1 a2 a3 k) :
    v5 a0 a1 a2 a3 k ∈ genClosure := by
  induction h with
  | zero =>
    rw [v5_zero]
    exact AddSubmonoid.zero_mem _
  | addA _ ih => exact step ih gA_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addE0 _ ih => exact step ih gE0_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addE1 _ ih => exact step ih gE1_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addE2 _ ih => exact step ih gE2_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addE3 _ ih => exact step ih gE3_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addB0 _ ih => exact step ih gB0_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addB1 _ ih => exact step ih gB1_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addB2 _ ih => exact step ih gB2_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addB3 _ ih => exact step ih gB3_mem (by omega) (by omega) (by omega) (by omega) (by omega)
  | addC _ ih => exact step ih gC_mem (by omega) (by omega) (by omega) (by omega) (by omega)

theorem mem_closure_iff_feasible {a0 a1 a2 a3 k : ℤ} :
    v5 a0 a1 a2 a3 k ∈ genClosure ↔ Aqarion.P2Gen.Feasible a0 a1 a2 a3 k := by
  constructor
  · intro h
    have h1 : v5 a0 a1 a2 a3 k ∈ feasSub := closure_le_feasSub h
    have h2 : Aqarion.P2Gen.Feasible (v5 a0 a1 a2 a3 k 0) (v5 a0 a1 a2 a3 k 1)
        (v5 a0 a1 a2 a3 k 2) (v5 a0 a1 a2 a3 k 3) (v5 a0 a1 a2 a3 k 4) := h1
    simpa [v5] using h2
  · intro h
    exact gen_mem_closure (Aqarion.P2Gen.feasible_gen h)

theorem gen_iff_mem_closure {a0 a1 a2 a3 k : ℤ} :
    Aqarion.P2Gen.Gen a0 a1 a2 a3 k ↔ v5 a0 a1 a2 a3 k ∈ genClosure :=
  Aqarion.P2Gen.gen_iff.trans mem_closure_iff_feasible.symm

theorem feasible_bridge {a0 a1 a2 a3 k : ℤ} :
    Aqarion.P2Arithmetic.Feasible a0 a1 a2 a3 k ↔ Aqarion.P2Gen.Feasible a0 a1 a2 a3 k := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    constructor <;> omega
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    constructor <;> omega

theorem strict_iff_closure_shift {a0 a1 a2 a3 k : ℤ} :
    Aqarion.P2Arithmetic.StrictFeasible a0 a1 a2 a3 k ↔
      v5 (a0 - 1) (a1 - 1) (a2 - 1) (a3 - 1) (k - 1) ∈ genClosure :=
  (Aqarion.P2Arithmetic.strict_iff_shifted (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (k := k)).trans (feasible_bridge.trans mem_closure_iff_feasible.symm)

end Aqarion.P2Bridge

#print axioms Aqarion.P2Bridge.mem_closure_iff_feasible
#print axioms Aqarion.P2Bridge.gen_iff_mem_closure
#print axioms Aqarion.P2Bridge.strict_iff_closure_shift
