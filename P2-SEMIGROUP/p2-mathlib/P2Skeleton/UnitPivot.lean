import Mathlib

set_option autoImplicit false

namespace P2Skeleton

/-- Matrix with r ones on the leading diagonal and zeros elsewhere. -/
def partialId (m n r : ℕ) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1 else 0

/-- SKELETON (sorry): the partial identity with r ones has rank r over a field. -/
theorem rank_partialId (m n r : ℕ) (hrm : r ≤ m) (hrn : r ≤ n)
    (K : Type) [Field K] :
    Matrix.rank ((partialId m n r).map (Int.castRingHom K)) = r := by
  sorry

/-- If unimodular integer row and column operations bring `M` to the partial
identity with `r` ones, then `M` has rank `r` over every field.
Proved here modulo `rank_partialId`. -/
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
