import FiniteRationalBridge
import Mathlib.LinearAlgebra.Matrix.Rank
import Lean.Elab.Tactic.Omega

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace AQARIONRank

/--
A nonzero rational row annihilating every column bounds the matrix rank.
Rows are states; columns are features.
-/
theorem rank_le_of_annihilator
    {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ)
    (v : Fin n → ℚ)
    (hv : v ≠ 0)
    (annihilates : ∀ j, (∑ i, v i * A i j) = 0) :
    A.rank ≤ n - 1 := by
  classical
  let B : Matrix (Fin 1) (Fin n) ℚ :=
    Matrix.of (fun _ i => v i)

  have hnot : ¬ ∀ i, v i = 0 := by
    intro hall
    apply hv
    funext i
    exact hall i

  obtain ⟨i, hi⟩ := not_forall.mp hnot

  let C : Matrix (Fin 1) (Fin 1) ℚ :=
    B.submatrix id (fun _ : Fin 1 => i)

  have hdet : C.det ≠ 0 := by
    rw [Matrix.det_fin_one]
    change v i ≠ 0
    exact hi

  have hCrank : C.rank = 1 := by
    simpa only [Fintype.card_fin] using
      (Matrix.rank_of_det_ne_zero hdet)

  have hBpos : 1 ≤ B.rank := by
    calc
      1 = C.rank := hCrank.symm
      _ ≤ B.rank :=
        Matrix.rank_submatrix_le B id (fun _ : Fin 1 => i)

  have hBA : B * A = 0 := by
    apply Matrix.ext
    intro r j
    rw [Matrix.mul_apply]
    change (∑ i : Fin n, v i * A i j) = 0
    exact annihilates j

  have htotal : B.rank + A.rank ≤ n := by
    simpa only [Fintype.card_fin] using
      (Matrix.rank_add_rank_le_card_of_mul_eq_zero hBA)

  omega

/-- A nonzero square minor certifies the corresponding lower rank bound. -/
theorem rank_ge_of_nonzero_minor
    {n m k : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ)
    (rows : Fin k → Fin n)
    (cols : Fin k → Fin m)
    (minor_nonzero : (A.submatrix rows cols).det ≠ 0) :
    k ≤ A.rank := by
  have hminor :
      (A.submatrix rows cols).rank = k := by
    simpa only [Fintype.card_fin] using
      (Matrix.rank_of_det_ne_zero minor_nonzero)
  calc
    k = (A.submatrix rows cols).rank := hminor.symm
    _ ≤ A.rank := Matrix.rank_submatrix_le A rows cols

/-- Exact matrix rank from an annihilator and a matching minor. -/
theorem rank_eq_of_annihilator_and_minor
    {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ)
    (v : Fin n → ℚ)
    (hv : v ≠ 0)
    (annihilates : ∀ j, (∑ i, v i * A i j) = 0)
    (rows : Fin (n - 1) → Fin n)
    (cols : Fin (n - 1) → Fin m)
    (minor_nonzero : (A.submatrix rows cols).det ≠ 0) :
    A.rank = n - 1 := by
  apply Nat.le_antisymm
  · exact rank_le_of_annihilator A v hv annihilates
  · exact rank_ge_of_nonzero_minor A rows cols minor_nonzero

/--
Feature tags:
  none   = constant one
  some t = observation at time t
-/
def temporalFeature
    {n : Nat}
    (T : Fin n → Fin n)
    (h : Fin n → ℚ) :
    Option Nat → Fin n → ℚ
  | none => fun _ => 1
  | some t => AQARIONTemporal.observeAt T h t

/-- The reconstructed temporal matrix, with states as rows. -/
def temporalMatrix
    {n m : Nat}
    (T : Fin n → Fin n)
    (h : Fin n → ℚ)
    (tags : Fin m → Option Nat) :
    Matrix (Fin n) (Fin m) ℚ :=
  fun i j => temporalFeature T h (tags j) i

/--
Every reconstructed feature is annihilated.
The constant-feature condition is explicit and separate.
-/
theorem temporal_columns_annihilated
    {n m : Nat}
    (T : Fin n → Fin n)
    (h v : Fin n → ℚ)
    (lambda : ℚ)
    (tags : Fin m → Option Nat)
    (constant_zero : (∑ i, v i) = 0)
    (initial_zero : AQARIONFinite.pairing v h = 0)
    (eigen :
      AQARIONFinite.push T v =
        AQARIONFinite.scaleWeight lambda v) :
    ∀ j, (∑ i, v i * temporalMatrix T h tags i j) = 0 := by
  intro j
  cases htag : tags j with
  | none =>
      simpa [temporalMatrix, temporalFeature, htag] using
        constant_zero
  | some t =>
      have hz :=
        AQARIONFinite.annihilates_all_observations
          T v h lambda eigen initial_zero t
      simpa [
        AQARIONFinite.pairing,
        temporalMatrix,
        temporalFeature,
        htag
      ] using hz

/-- Upper rank bound for any selected finite temporal-feature family. -/
theorem temporal_matrix_rank_le
    {n m : Nat}
    (T : Fin n → Fin n)
    (h v : Fin n → ℚ)
    (lambda : ℚ)
    (tags : Fin m → Option Nat)
    (hv : v ≠ 0)
    (constant_zero : (∑ i, v i) = 0)
    (initial_zero : AQARIONFinite.pairing v h = 0)
    (eigen :
      AQARIONFinite.push T v =
        AQARIONFinite.scaleWeight lambda v) :
    (temporalMatrix T h tags).rank ≤ n - 1 := by
  apply rank_le_of_annihilator (temporalMatrix T h tags) v hv
  exact temporal_columns_annihilated
    T h v lambda tags constant_zero initial_zero eigen

/--
Exact rank for the reconstructed finite temporal matrix,
conditional on its matching nonzero minor.
-/
theorem temporal_matrix_rank_eq
    {n m : Nat}
    (T : Fin n → Fin n)
    (h v : Fin n → ℚ)
    (lambda : ℚ)
    (tags : Fin m → Option Nat)
    (hv : v ≠ 0)
    (constant_zero : (∑ i, v i) = 0)
    (initial_zero : AQARIONFinite.pairing v h = 0)
    (eigen :
      AQARIONFinite.push T v =
        AQARIONFinite.scaleWeight lambda v)
    (rows : Fin (n - 1) → Fin n)
    (cols : Fin (n - 1) → Fin m)
    (minor_nonzero :
      ((temporalMatrix T h tags).submatrix rows cols).det ≠ 0) :
    (temporalMatrix T h tags).rank = n - 1 := by
  apply rank_eq_of_annihilator_and_minor
    (temporalMatrix T h tags) v hv
    (temporal_columns_annihilated
      T h v lambda tags constant_zero initial_zero eigen)
    rows cols minor_nonzero

end AQARIONRank

#check AQARIONRank.rank_le_of_annihilator
#check AQARIONRank.rank_ge_of_nonzero_minor
#check AQARIONRank.rank_eq_of_annihilator_and_minor
#check AQARIONRank.temporal_columns_annihilated
#check AQARIONRank.temporal_matrix_rank_le
#check AQARIONRank.temporal_matrix_rank_eq

#print axioms AQARIONRank.rank_le_of_annihilator
#print axioms AQARIONRank.rank_ge_of_nonzero_minor
#print axioms AQARIONRank.rank_eq_of_annihilator_and_minor
#print axioms AQARIONRank.temporal_columns_annihilated
#print axioms AQARIONRank.temporal_matrix_rank_le
#print axioms AQARIONRank.temporal_matrix_rank_eq
