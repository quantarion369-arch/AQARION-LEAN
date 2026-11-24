import Mathlib

set_option autoImplicit false

namespace P2Skeleton

/-- SKELETON: statement only, proof is `sorry`. Not a verified result.
Matrix with r ones on the leading diagonal and zeros elsewhere. -/
def partialId (m n r : ℕ) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1 else 0

/-- SKELETON: if unimodular integer row and column operations bring `M` to the
partial identity with `r` ones, then `M` has rank `r` over every field. -/
theorem rank_of_unit_pivot_normal_form
    (m n r : ℕ) (hrm : r ≤ m) (hrn : r ≤ n)
    (M : Matrix (Fin m) (Fin n) ℤ)
    (U : Matrix (Fin m) (Fin m) ℤ) (V : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = partialId m n r)
    (K : Type) [Field K] :
    Matrix.rank (M.map (fun x : ℤ => (x : K))) = r := by
  sorry

end P2Skeleton

#print axioms P2Skeleton.rank_of_unit_pivot_normal_form
