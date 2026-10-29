import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import TemporalAnnihilation

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace AQARIONFinite

/-- Finite rational sums can be interchanged, by induction. -/
private theorem sum_swap
    {α β : Type*}
    (s : Finset α) (t : Finset β)
    (f : α → β → ℚ) :
    (∑ x ∈ s, ∑ y ∈ t, f x y) =
      ∑ y ∈ t, ∑ x ∈ s, f x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
      rw [ih]


/-- Exact finite rational weighted pairing. -/
def pairing {n : Nat}
    (v g : Fin n → ℚ) : ℚ :=
  ∑ x, v x * g x

/-- Push weights into their transition destinations. -/
def push {n : Nat}
    (T : Fin n → Fin n)
    (v : Fin n → ℚ) : Fin n → ℚ :=
  fun y => ∑ x, if T x = y then v x else 0

def scaleWeight {n : Nat}
    (a : ℚ) (v : Fin n → ℚ) : Fin n → ℚ :=
  fun x => a * v x

/--
Pushforward is dual to pulling observations back along T.
T need not be invertible.
-/
theorem duality
    {n : Nat}
    (T : Fin n → Fin n)
    (v g : Fin n → ℚ) :
    pairing v (fun x => g (T x)) =
      pairing (push T v) g := by
  unfold pairing push
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [sum_swap]
  simp

theorem homogeneous
    {n : Nat}
    (a : ℚ)
    (v g : Fin n → ℚ) :
    pairing (scaleWeight a v) g =
      a * pairing v g := by
  simp only [
    pairing,
    scaleWeight,
    Finset.mul_sum,
    mul_assoc
  ]

/--
Finite rational temporal annihilation.

Unlike the abstract predecessor, duality and homogeneity
are established above from the actual finite-sum definitions.
-/
theorem annihilates_all_observations
    {n : Nat}
    (T : Fin n → Fin n)
    (v h : Fin n → ℚ)
    (lambda : ℚ)
    (eigen : push T v = scaleWeight lambda v)
    (initial_zero : pairing v h = 0) :
    ∀ t : Nat,
      pairing v (AQARIONTemporal.observeAt T h t) = 0 := by
  exact AQARIONTemporal.annihilates_all_observations
    T h pairing (push T) scaleWeight
    (fun a b : ℚ => a * b)
    0 lambda v
    (mul_zero lambda)
    (fun g => duality T v g)
    eigen
    (fun g => homogeneous lambda v g)
    initial_zero

end AQARIONFinite

#check AQARIONFinite.duality
#check AQARIONFinite.homogeneous
#check AQARIONFinite.annihilates_all_observations

#print axioms AQARIONFinite.duality
#print axioms AQARIONFinite.homogeneous
#print axioms AQARIONFinite.annihilates_all_observations

#print axioms AQARIONFinite.duality
#print axioms AQARIONFinite.homogeneous
#print axioms AQARIONFinite.annihilates_all_observations
