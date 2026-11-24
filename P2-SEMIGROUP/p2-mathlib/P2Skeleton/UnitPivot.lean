import Mathlib

set_option autoImplicit false

namespace P2Skeleton

/-- Matrix with r ones on the leading diagonal and zeros elsewhere. -/
def partialId (m n r : ℕ) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1 else 0

def pMat (m r : ℕ) (K : Type) [Field K] : Matrix (Fin m) (Fin r) K :=
  Matrix.of fun i k => if (i : ℕ) = (k : ℕ) then 1 else 0

def qMat (n r : ℕ) (K : Type) [Field K] : Matrix (Fin r) (Fin n) K :=
  Matrix.of fun k j => if (k : ℕ) = (j : ℕ) then 1 else 0

theorem pMat_mul_qMat (m n r : ℕ) (K : Type) [Field K] :
    pMat m r K * qMat n r K = (partialId m n r).map (Int.castRingHom K) := by
  ext i j
  simp only [Matrix.mul_apply, pMat, qMat, Matrix.of_apply, Matrix.map_apply, partialId]
  by_cases hi : (i : ℕ) < r
  · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin r)]
    · by_cases hij : (i : ℕ) = (j : ℕ)
      · simp [hij, hi]
      · simp [hij, hi]
    · intro k _ hk
      have hne : (i : ℕ) ≠ (k : ℕ) := by
        intro h
        exact hk (Fin.ext h.symm)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro k _
      have hne : (i : ℕ) ≠ (k : ℕ) := by
        intro h
        apply hi
        rw [h]
        exact k.2
      simp [hne]

theorem pMat_transpose_mul (m r : ℕ) (hrm : r ≤ m) (K : Type) [Field K] :
    (pMat m r K)ᵀ * pMat m r K = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pMat, Matrix.of_apply, Matrix.one_apply]
  have hk : (k : ℕ) < m := lt_of_lt_of_le k.2 hrm
  rw [Finset.sum_eq_single (⟨(k : ℕ), hk⟩ : Fin m)]
  · by_cases hkl : k = l
    · subst hkl
      simp
    · have hne : (k : ℕ) ≠ (l : ℕ) := fun h => hkl (Fin.ext h)
      simp [hkl, hne]
  · intro i _ hi
    by_cases h : (i : ℕ) = (k : ℕ)
    · exact absurd (Fin.ext h) hi
    · simp [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qMat_mul_transpose (n r : ℕ) (hrn : r ≤ n) (K : Type) [Field K] :
    qMat n r K * (qMat n r K)ᵀ = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, qMat, Matrix.of_apply, Matrix.one_apply]
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.2 hrn
  rw [Finset.sum_eq_single (⟨(k : ℕ), hk⟩ : Fin n)]
  · by_cases hkl : k = l
    · subst hkl
      simp
    · have hne : (l : ℕ) ≠ (k : ℕ) := fun h => hkl (Fin.ext h.symm)
      simp [hkl, hne]
  · intro j _ hj
    by_cases h : (k : ℕ) = (j : ℕ)
    · exact absurd (Fin.ext h.symm) hj
    · simp [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The partial identity with r ones has rank r over a field. -/
theorem rank_partialId (m n r : ℕ) (hrm : r ≤ m) (hrn : r ≤ n)
    (K : Type) [Field K] :
    Matrix.rank ((partialId m n r).map (Int.castRingHom K)) = r := by
  rw [← pMat_mul_qMat m n r K]
  have hle : Matrix.rank (pMat m r K * qMat n r K) ≤ r := by
    calc Matrix.rank (pMat m r K * qMat n r K) ≤ Matrix.rank (pMat m r K) :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := by
          first
            | exact Matrix.rank_le_width _
            | exact Matrix.rank_le_card_width _
      _ = r := Fintype.card_fin r
  have hone : (pMat m r K)ᵀ * (pMat m r K * qMat n r K) * (qMat n r K)ᵀ = 1 := by
    calc (pMat m r K)ᵀ * (pMat m r K * qMat n r K) * (qMat n r K)ᵀ
        = ((pMat m r K)ᵀ * pMat m r K) * (qMat n r K * (qMat n r K)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [pMat_transpose_mul m r hrm K, qMat_mul_transpose n r hrn K, Matrix.mul_one]
  have hge : r ≤ Matrix.rank (pMat m r K * qMat n r K) := by
    calc r = Matrix.rank (1 : Matrix (Fin r) (Fin r) K) := by
          rw [Matrix.rank_one, Fintype.card_fin]
      _ = Matrix.rank ((pMat m r K)ᵀ * (pMat m r K * qMat n r K) * (qMat n r K)ᵀ) := by
          rw [hone]
      _ ≤ Matrix.rank ((pMat m r K)ᵀ * (pMat m r K * qMat n r K)) :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Matrix.rank (pMat m r K * qMat n r K) :=
          Matrix.rank_mul_le_right _ _
  exact le_antisymm hle hge

/-- If unimodular integer row and column operations bring `M` to the partial
identity with `r` ones, then `M` has rank `r` over every field.
Uses `rank_partialId` above. -/
theorem rank_of_unit_pivot_normal_form
    (m n r : ℕ) (hrm : r ≤ m) (hrn : r ≤ n)
    (M : Matrix (Fin m) (Fin n) ℤ)
    (U : Matrix (Fin m) (Fin m) ℤ) (V : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = partialId m n r)
    (K : Type) [Field K] :
    Matrix.rank (M.map (Int.castRingHom K)) = r := by
  have h1 : (U.map (Int.castRingHom K)) * (M.map (Int.castRingHom K)) *
      (V.map (Int.castRingHom K)) = (partialId m n r).map (Int.castRingHom K) := by
    rw [← h, Matrix.map_mul, Matrix.map_mul]
  have hU' : IsUnit (U.map (Int.castRingHom K)).det := by
    have h0 := hU.map (Int.castRingHom K)
    first
      | (rw [RingHom.map_det] at h0; simpa using h0)
      | (simpa [RingHom.map_det] using h0)
      | (rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact h0)
  have hV' : IsUnit (V.map (Int.castRingHom K)).det := by
    have h0 := hV.map (Int.castRingHom K)
    first
      | (rw [RingHom.map_det] at h0; simpa using h0)
      | (simpa [RingHom.map_det] using h0)
      | (rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact h0)
  have hrk : Matrix.rank (M.map (Int.castRingHom K)) =
      Matrix.rank ((U.map (Int.castRingHom K)) * (M.map (Int.castRingHom K)) *
        (V.map (Int.castRingHom K))) := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU']
  rw [hrk, h1]
  exact rank_partialId m n r hrm hrn K

end P2Skeleton

#print axioms P2Skeleton.rank_of_unit_pivot_normal_form
