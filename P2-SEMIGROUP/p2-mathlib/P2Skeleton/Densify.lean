import Mathlib

set_option autoImplicit false

namespace P2Skeleton

/-- Dense row of length `nc` from sparse (column, value) pairs; missing columns are zero. -/
def sparseRow (nc : ℕ) (r : List (ℕ × ℤ)) : List ℤ :=
  (List.range nc).map (fun b => ((r.find? (fun p => p.1 == b)).map Prod.snd).getD 0)

/-- Dense table from sparse rows. -/
def densify (nc : ℕ) (rs : List (List (ℕ × ℤ))) : List (List ℤ) :=
  rs.map (sparseRow nc)

end P2Skeleton
