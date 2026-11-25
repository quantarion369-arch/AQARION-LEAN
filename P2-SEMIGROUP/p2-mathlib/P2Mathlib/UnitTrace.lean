import Mathlib

set_option autoImplicit false

namespace P2Mathlib

/-- Integer Schur complement for a pivot entry equal to 1 or -1 (its own inverse). -/
def schur {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℤ) (i : ι) (j : κ) : Matrix {a // a ≠ i} {b // b ≠ j} ℤ :=
  Matrix.of fun a b => M a b - M a j * M i j * M i b

/-- Schur complement over a field, with the pivot inverted. -/
def schurK {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ) :
    Matrix {a // a ≠ i} {b // b ≠ j} K :=
  Matrix.of fun a b => M a b - M a j * (M i j)⁻¹ * M i b

/-- A unit-pivot trace of length r: r successive pivots equal to 1 or -1, each followed by
Schur elimination, ending in the zero matrix. -/
def UnitTrace : ℕ → ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
    Matrix ι κ ℤ → Prop
  | 0 => fun (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (M : Matrix ι κ ℤ) => M = 0
  | r + 1 => fun (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (M : Matrix ι κ ℤ) =>
      ∃ (i : ι) (j : κ), (M i j = 1 ∨ M i j = -1) ∧
        UnitTrace r {a // a ≠ i} {b // b ≠ j} (schur M i j)

/-- Extension by zero from the columns away from `j`. -/
def extZero {κ : Type} [DecidableEq κ] {K : Type} [Field K] (j : κ) :
    ({b // b ≠ j} → K) →ₗ[K] (κ → K) where
  toFun f := fun b => if h : b = j then 0 else f ⟨b, h⟩
  map_add' f g := by
    funext b
    by_cases h : b = j <;> simp [h]
  map_smul' c f := by
    funext b
    by_cases h : b = j <;> simp [h]

theorem extZero_injective {κ : Type} [DecidableEq κ] {K : Type} [Field K] (j : κ) :
    Function.Injective (extZero (K := K) j) := by
  intro f g hfg
  funext b
  have h1 := congrFun hfg b.1
  simpa [extZero, b.2] using h1

/-- Row `a` after clearing column `j` with the pivot row `i`, as a vector on all columns. -/
def redRow {ι κ : Type} {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ)
    (a : {a // a ≠ i}) : κ → K :=
  fun b => M a b - M a j * (M i j)⁻¹ * M i b

theorem redRow_apply_j {ι κ : Type} {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ)
    (h : M i j ≠ 0) (a : {a // a ≠ i}) : redRow M i j a j = 0 := by
  first
    | (simp [redRow, h]; done)
    | (simp [redRow, mul_assoc, inv_mul_cancel₀ h]; done)
    | (unfold redRow; field_simp; ring)

theorem extZero_schurK_row {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ)
    (h : M i j ≠ 0) (a : {a // a ≠ i}) :
    extZero j ((schurK M i j).row a) = redRow M i j a := by
  funext b
  by_cases hb : b = j
  · have e : redRow M i j a b = 0 := by
      rw [hb]
      exact redRow_apply_j M i j h a
    have e2 : extZero j ((schurK M i j).row a) b = 0 := by
      simp [extZero, hb]
    exact e2.trans e.symm
  · simp [extZero, hb, redRow, schurK, Matrix.row]

/-- Rank of a matrix with a nonzero pivot is one plus the rank of its Schur complement. -/
theorem rank_schurK_step {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ) (h : M i j ≠ 0) :
    Matrix.rank M = Matrix.rank (schurK M i j) + 1 := by
  have hrow : Matrix.rank M = Module.finrank K (Submodule.span K (Set.range M.row)) := by
    first
      | exact Matrix.rank_eq_finrank_span_row M
      | exact (Matrix.finrank_span_range_row M).symm
  have hrowS : Matrix.rank (schurK M i j) =
      Module.finrank K (Submodule.span K (Set.range (schurK M i j).row)) := by
    first
      | exact Matrix.rank_eq_finrank_span_row _
      | exact (Matrix.finrank_span_range_row _).symm
  have hspan : Submodule.span K (Set.range M.row) =
      Submodule.span K {M i} ⊔ Submodule.span K (Set.range (redRow M i j)) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨a, rfl⟩
      by_cases ha : a = i
      · have h1 : M.row a = M i := by simp [Matrix.row, ha]
        rw [h1]
        exact Submodule.mem_sup_left (Submodule.subset_span rfl)
      · have h1 : M.row a = redRow M i j ⟨a, ha⟩ + (M a j * (M i j)⁻¹) • M i := by
          funext b
          simp [Matrix.row, redRow] <;> ring
        rw [h1]
        exact Submodule.add_mem _
          (Submodule.mem_sup_right (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span rfl)))
    · apply sup_le
      · apply Submodule.span_le.2
        rintro _ rfl
        exact Submodule.subset_span ⟨i, rfl⟩
      · apply Submodule.span_le.2
        rintro _ ⟨a, rfl⟩
        have h1 : redRow M i j a = M.row a - (M a j * (M i j)⁻¹) • M.row i := by
          funext b
          simp [Matrix.row, redRow, mul_assoc]
        rw [h1]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hinf : Submodule.span K {M i} ⊓ Submodule.span K (Set.range (redRow M i j)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hv1
    have hle : Submodule.span K (Set.range (redRow M i j)) ≤
        LinearMap.ker (LinearMap.proj j : (κ → K) →ₗ[K] K) := by
      apply Submodule.span_le.2
      rintro _ ⟨a, rfl⟩
      simpa using redRow_apply_j M i j h a
    have hvj : v j = 0 := by
      have h2 := hle hv2
      simpa using h2
    have e := congrFun hs j
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [hvj] at e
    rcases mul_eq_zero.1 e with h0 | h0
    · rw [← hs, h0, zero_smul]
    · exact absurd h0 h
  have hfin1 : Module.finrank K (Submodule.span K {M i}) = 1 := by
    apply finrank_span_singleton
    intro h0
    apply h
    have := congrFun h0 j
    simpa using this
  have hfun : redRow M i j = (extZero j) ∘ (schurK M i j).row :=
    funext fun a => (extZero_schurK_row M i j h a).symm
  have hmap : Submodule.span K (Set.range (redRow M i j)) =
      (Submodule.span K (Set.range (schurK M i j).row)).map (extZero j) := by
    rw [Submodule.map_span, ← Set.range_comp, ← hfun]
  have hW : Module.finrank K (Submodule.span K (Set.range (redRow M i j))) =
      Module.finrank K (Submodule.span K (Set.range (schurK M i j).row)) := by
    rw [hmap]
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (extZero j) (extZero_injective j) _)).symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {M i})
    (Submodule.span K (Set.range (redRow M i j)))
  rw [hinf, finrank_bot, add_zero, hfin1] at hsum
  rw [hrow, hrowS, hspan, hsum, hW]
  omega

theorem map_schur {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (M : Matrix ι κ ℤ) (i : ι) (j : κ)
    (h : M i j = 1 ∨ M i j = -1) :
    (schur M i j).map (Int.castRingHom K) = schurK (M.map (Int.castRingHom K)) i j := by
  ext a b
  rcases h with h | h <;>
    first
      | (simp [schur, schurK, h]; done)
      | (simp [schur, schurK, h]; ring)

theorem rank_of_unitTrace (K : Type) [Field K] :
    ∀ (r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (M : Matrix ι κ ℤ), UnitTrace r ι κ M →
        Matrix.rank (M.map (Int.castRingHom K)) = r := by
  intro r
  induction r with
  | zero =>
    intro ι κ _ _ _ _ M h
    have h0 : M = 0 := h
    subst h0
    simp
  | succ r ih =>
    intro ι κ _ _ _ _ M h
    obtain ⟨i, j, hij, h'⟩ := h
    have hne : (M.map (Int.castRingHom K)) i j ≠ 0 := by
      rcases hij with h1 | h1 <;> simp [h1]
    rw [rank_schurK_step _ i j hne, ← map_schur (K := K) M i j hij, ih _ _ _ h']

end P2Mathlib

#print axioms P2Mathlib.rank_of_unitTrace
