import Mathlib

set_option autoImplicit false

namespace P2Skeleton

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

/-- SKELETON (sorry): rank of a matrix with a nonzero pivot is one plus the rank of its
Schur complement. -/
theorem rank_schurK_step {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (M : Matrix ι κ K) (i : ι) (j : κ) (h : M i j ≠ 0) :
    Matrix.rank M = Matrix.rank (schurK M i j) + 1 := by
  sorry

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

end P2Skeleton

#print axioms P2Skeleton.rank_of_unitTrace
