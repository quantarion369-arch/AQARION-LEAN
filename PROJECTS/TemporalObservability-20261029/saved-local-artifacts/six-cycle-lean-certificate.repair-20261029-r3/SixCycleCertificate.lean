import TemporalMatrixRank

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace AQARIONSixCycle

def T (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

def h (i : Fin 6) : ℚ :=
  if i.val < 2 then 1 else 0

def v (i : Fin 6) : ℚ :=
  if i.val % 2 = 0 then 1 else -1

def tags (j : Fin 5) : Option Nat :=
  if j.val = 0 then none else some (j.val - 1)

def selectedStates (i : Fin 5) : Fin 6 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide : 5 < 6)⟩

def A : Matrix (Fin 6) (Fin 5) ℚ :=
  AQARIONRank.temporalMatrix T h tags

def minor : Matrix (Fin 5) (Fin 5) ℚ :=
  A.submatrix selectedStates id

/-- Explicit right-inverse witness for the selected minor. -/
def inverseWitness : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.of (fun i j =>
    match i.val, j.val with
    | 0, 2 => 1
    | 1, 1 => 1
    | 1, 2 => -1
    | 2, 0 => 1
    | 2, 1 => -1
    | 3, 3 => -1
    | 3, 4 => 1
    | 4, 2 => -1
    | 4, 3 => 1
    | _, _ => 0)

/-- This orientation matches the Python checker. -/
def pythonMinor : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.of (fun feature state =>
    AQARIONRank.temporalFeature T h
      (tags feature) (selectedStates state))

theorem full_support : ∀ i : Fin 6, v i ≠ 0 := by
  decide

theorem v_nonzero : v ≠ 0 := by
  intro hz
  exact (full_support (0 : Fin 6)) (congrFun hz 0)

theorem constant_zero : (∑ i : Fin 6, v i) = 0 := by
  norm_num [v]

theorem initial_zero : AQARIONFinite.pairing v h = 0 := by
  norm_num [AQARIONFinite.pairing, v, h]

theorem eigen :
    AQARIONFinite.push T v =
      AQARIONFinite.scaleWeight (-1) v := by
  funext i
  fin_cases i <;>
    norm_num [AQARIONFinite.push,
      AQARIONFinite.scaleWeight, T, v]

theorem minor_mul_inverse :
    minor * inverseWitness = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, minor, A, inverseWitness,
      AQARIONRank.temporalMatrix,
      AQARIONRank.temporalFeature,
      AQARIONTemporal.observeAt, selectedStates, tags, T, h]

theorem minor_nonzero : minor.det ≠ 0 := by
  have hproduct :
      minor.det * inverseWitness.det = (1 : ℚ) := by
    rw [← Matrix.det_mul, minor_mul_inverse, Matrix.det_one]
  intro hz
  rw [hz, zero_mul] at hproduct
  exact zero_ne_one hproduct

theorem python_minor_eq_transpose :
    pythonMinor = minor.transpose := by
  rfl

theorem python_minor_nonzero : pythonMinor.det ≠ 0 := by
  rw [python_minor_eq_transpose, Matrix.det_transpose]
  exact minor_nonzero

theorem rank_five : A.rank = 5 := by
  exact AQARIONRank.temporal_matrix_rank_eq
    T h v (-1) tags
    v_nonzero
    constant_zero
    initial_zero
    eigen
    selectedStates
    id
    minor_nonzero

theorem all_observations_annihilated :
    ∀ t : Nat,
      AQARIONFinite.pairing v
        (AQARIONTemporal.observeAt T h t) = 0 :=
  AQARIONFinite.annihilates_all_observations
    T v h (-1) eigen initial_zero

end AQARIONSixCycle

#check AQARIONSixCycle.rank_five
#check AQARIONSixCycle.full_support
#check AQARIONSixCycle.all_observations_annihilated

#print axioms AQARIONSixCycle.full_support
#print axioms AQARIONSixCycle.v_nonzero
#print axioms AQARIONSixCycle.constant_zero
#print axioms AQARIONSixCycle.initial_zero
#print axioms AQARIONSixCycle.eigen
#print axioms AQARIONSixCycle.minor_mul_inverse
#print axioms AQARIONSixCycle.minor_nonzero
#print axioms AQARIONSixCycle.python_minor_eq_transpose
#print axioms AQARIONSixCycle.python_minor_nonzero
#print axioms AQARIONSixCycle.rank_five
#print axioms AQARIONSixCycle.all_observations_annihilated
