import Mathlib

set_option autoImplicit false

namespace P2Skeleton

/-- One elimination step: use row `i` and column `j` to clear column `j` from every other row. -/
def pivStep {ι κ : Type} [DecidableEq ι] (M : ι → κ → ℤ) (i : ι) (j : κ) : ι → κ → ℤ :=
  fun a b => if a = i then M a b else M a b - M a j * M i j * M i b

/-- Row `a` of the integer table `M`, cast into `K`. -/
def rowF {ι κ : Type} (K : Type) [Field K] (M : ι → κ → ℤ) (a : ι) : κ → K :=
  fun b => ((M a b : ℤ) : K)

/-- Row space over `K` of the active rows `s`. -/
abbrev rowSp {ι κ : Type} (K : Type) [Field K] (M : ι → κ → ℤ) (s : Finset ι) :
    Submodule K (κ → K) :=
  Submodule.span K (rowF K M '' (s : Set ι))

/-- Replay of a row-only unit-pivot trace: each step has a plus or minus one entry at the pivot,
and the pivot row leaves the active set; at the end every active row is zero. -/
inductive RowTrace {ι κ : Type} [DecidableEq ι] :
    List (ι × κ) → Finset ι → (ι → κ → ℤ) → Prop
  | nil (s : Finset ι) (M : ι → κ → ℤ) (h : ∀ a ∈ s, ∀ b, M a b = 0) : RowTrace [] s M
  | cons (i : ι) (j : κ) (t : List (ι × κ)) (s : Finset ι) (M : ι → κ → ℤ)
      (hi : i ∈ s) (hu : M i j = 1 ∨ M i j = -1)
      (h : RowTrace t (s.erase i) (pivStep M i j)) : RowTrace ((i, j) :: t) s M

theorem rowF_pivStep_ne {ι κ : Type} [DecidableEq ι] (K : Type) [Field K]
    (M : ι → κ → ℤ) (i : ι) (j : κ) (a : ι) (ha : a ≠ i) :
    rowF K (pivStep M i j) a = rowF K M a - ((M a j * M i j : ℤ) : K) • rowF K M i := by
  funext b
  simp only [rowF, pivStep, if_neg ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  first | (push_cast; ring) | push_cast

theorem rowF_pivStep_apply_j {ι κ : Type} [DecidableEq ι] (K : Type) [Field K]
    (M : ι → κ → ℤ) (i : ι) (j : κ) (hu : M i j = 1 ∨ M i j = -1) (a : ι) (ha : a ≠ i) :
    rowF K (pivStep M i j) a j = 0 := by
  simp only [rowF, pivStep, if_neg ha]
  rcases hu with h | h <;> simp [h]

theorem finrank_rowSp_step {ι κ : Type} [Fintype κ] [DecidableEq ι] (K : Type) [Field K]
    (M : ι → κ → ℤ) (s : Finset ι) (i : ι) (j : κ) (hi : i ∈ s)
    (hu : M i j = 1 ∨ M i j = -1) :
    Module.finrank K (rowSp K M s) =
      Module.finrank K (rowSp K (pivStep M i j) (s.erase i)) + 1 := by
  have hU : rowF K M i j ≠ 0 := by
    rcases hu with h | h <;> simp [rowF, h]
  have hspan : rowSp K M s =
      Submodule.span K {rowF K M i} ⊔ rowSp K (pivStep M i j) (s.erase i) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨a, ha, rfl⟩
      by_cases hai : a = i
      · subst hai
        exact Submodule.mem_sup_left (Submodule.subset_span rfl)
      · have h1 : rowF K M a = rowF K (pivStep M i j) a +
            ((M a j * M i j : ℤ) : K) • rowF K M i := by
          rw [rowF_pivStep_ne K M i j a hai]
          abel
        rw [h1]
        refine Submodule.add_mem _ (Submodule.mem_sup_right ?_)
          (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span rfl)))
        exact Submodule.subset_span
          ⟨a, by simp [Finset.mem_erase, hai, Finset.mem_coe.1 ha], rfl⟩
    · apply sup_le
      · apply Submodule.span_le.2
        rintro _ rfl
        exact Submodule.subset_span ⟨i, Finset.mem_coe.2 hi, rfl⟩
      · apply Submodule.span_le.2
        rintro _ ⟨a, ha, rfl⟩
        have hai : a ≠ i := (Finset.mem_erase.1 (Finset.mem_coe.1 ha)).1
        have has : a ∈ s := (Finset.mem_erase.1 (Finset.mem_coe.1 ha)).2
        rw [rowF_pivStep_ne K M i j a hai]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, Finset.mem_coe.2 has, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.2 hi, rfl⟩))
  have hinf : Submodule.span K {rowF K M i} ⊓ rowSp K (pivStep M i j) (s.erase i) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hv1
    have hle : rowSp K (pivStep M i j) (s.erase i) ≤
        LinearMap.ker (LinearMap.proj j : (κ → K) →ₗ[K] K) := by
      apply Submodule.span_le.2
      rintro _ ⟨a, ha, rfl⟩
      have hai : a ≠ i := (Finset.mem_erase.1 (Finset.mem_coe.1 ha)).1
      simpa using rowF_pivStep_apply_j K M i j hu a hai
    have hvj : v j = 0 := by
      have h2 := hle hv2
      simpa using h2
    have e := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [hvj] at e
    rcases mul_eq_zero.1 e with h0 | h0
    · rw [← hc, h0, zero_smul]
    · exact absurd h0 hU
  have hfin1 : Module.finrank K (Submodule.span K {rowF K M i}) = 1 :=
    finrank_span_singleton (fun h0 => hU (congrFun h0 j))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {rowF K M i})
    (rowSp K (pivStep M i j) (s.erase i))
  rw [hinf, finrank_bot, add_zero, hfin1] at hsum
  rw [hspan, hsum]
  omega

theorem rank_rowTrace {ι κ : Type} [DecidableEq ι] [Fintype κ] (K : Type) [Field K] :
    ∀ (t : List (ι × κ)) (s : Finset ι) (M : ι → κ → ℤ), RowTrace t s M →
      Module.finrank K (rowSp K M s) = t.length := by
  intro t s M h
  induction h with
  | nil s M hz =>
      have hb : rowSp K M s = ⊥ := by
        rw [eq_bot_iff]
        apply Submodule.span_le.2
        rintro _ ⟨a, ha, rfl⟩
        have h0 : rowF K M a = 0 := by
          funext b
          simp [rowF, hz a (Finset.mem_coe.1 ha) b]
        rw [h0]
        exact Submodule.zero_mem _
      rw [hb]
      simp
  | cons i j t s M hi hu _ ih =>
      rw [finrank_rowSp_step K M s i j hi hu, ih]
      simp

theorem rank_of_rowTrace {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (K : Type) [Field K] (M : ι → κ → ℤ) (t : List (ι × κ))
    (h : RowTrace t Finset.univ M) :
    Matrix.rank (Matrix.of fun a b => ((M a b : ℤ) : K)) = t.length := by
  have h1 := rank_rowTrace K t Finset.univ M h
  have h2 : rowSp K M Finset.univ = Submodule.span K
      (Set.range (Matrix.of fun a b => ((M a b : ℤ) : K)).row) := by
    unfold rowSp
    congr 1
    rw [Finset.coe_univ, Set.image_univ]
    rfl
  have hr : Matrix.rank (Matrix.of fun a b => ((M a b : ℤ) : K)) = Module.finrank K
      (Submodule.span K (Set.range (Matrix.of fun a b => ((M a b : ℤ) : K)).row)) := by
    first
      | exact Matrix.rank_eq_finrank_span_row _
      | exact (Matrix.finrank_span_range_row _).symm
  rw [hr, ← h2, h1]

end P2Skeleton

#print axioms P2Skeleton.rank_rowTrace
#print axioms P2Skeleton.rank_of_rowTrace
