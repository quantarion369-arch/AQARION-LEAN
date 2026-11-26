import Denom5CylinderProbabilityFixed

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5ObservedAllHistoryMarkov

open AQARION.Denom5ExplicitObserved
open AQARION.Denom5CylinderProbabilityFixed

def histMass (u : Rat × Rat) : Rat := u.1 + u.2

theorem observedNext_true (y : Rat × Rat) :
    observedNext y true = observedBlockA (observedStep y) := rfl

theorem observedNext_false (y : Rat × Rat) :
    observedNext y false = observedBlockB (observedStep y) := rfl

theorem observedTail_append_single (w : List Bool) (c : Bool) :
    ∀ y : Rat × Rat,
      observedTail y (w ++ [c]) = observedNext (observedTail y w) c := by
  induction w with
  | nil =>
      intro y
      rfl
  | cons b bs ih =>
      intro y
      change observedTail (observedNext y b) (bs ++ [c]) =
        observedNext (observedTail (observedNext y b) bs) c
      exact ih _

theorem next_true_support (y : Rat × Rat) :
    (observedNext y true).2 = 0 := rfl

theorem next_false_support (y : Rat × Rat) :
    (observedNext y false).1 = 0 := rfl

theorem start_support_A (y : Rat × Rat) :
    (observedBlockA y).2 = 0 := rfl

theorem start_support_B (y : Rat × Rat) :
    (observedBlockB y).1 = 0 := rfl

theorem from_A_supported (v : Rat × Rat) (h : v.2 = 0) :
    5 * histMass (observedNext v true) = 3 * histMass v ∧
    5 * histMass (observedNext v false) = 2 * histMass v := by
  constructor <;>
    simp only [histMass, observedNext_true, observedNext_false,
      observedBlockA, observedBlockB, observedStep] <;>
    grind

theorem from_B_supported (v : Rat × Rat) (h : v.1 = 0) :
    5 * histMass (observedNext v true) = 2 * histMass v ∧
    5 * histMass (observedNext v false) = 3 * histMass v := by
  constructor <;>
    simp only [histMass, observedNext_true, observedNext_false,
      observedBlockA, observedBlockB, observedStep] <;>
    grind

theorem history_support_true (s : Rat × Rat) (w : List Bool) :
    (observedTail s (w ++ [true])).2 = 0 := by
  rw [observedTail_append_single]
  exact next_true_support _

theorem history_support_false (s : Rat × Rat) (w : List Bool) :
    (observedTail s (w ++ [false])).1 = 0 := by
  rw [observedTail_append_single]
  exact next_false_support _

theorem all_histories_after_A (s : Rat × Rat) (w : List Bool) :
    5 * histMass (observedNext (observedTail s (w ++ [true])) true) =
      3 * histMass (observedTail s (w ++ [true])) ∧
    5 * histMass (observedNext (observedTail s (w ++ [true])) false) =
      2 * histMass (observedTail s (w ++ [true])) :=
  from_A_supported _ (history_support_true s w)

theorem all_histories_after_B (s : Rat × Rat) (w : List Bool) :
    5 * histMass (observedNext (observedTail s (w ++ [false])) true) =
      2 * histMass (observedTail s (w ++ [false])) ∧
    5 * histMass (observedNext (observedTail s (w ++ [false])) false) =
      3 * histMass (observedTail s (w ++ [false])) :=
  from_B_supported _ (history_support_false s w)

#print axioms observedNext_true
#print axioms observedNext_false
#print axioms observedTail_append_single
#print axioms next_true_support
#print axioms next_false_support
#print axioms start_support_A
#print axioms start_support_B
#print axioms from_A_supported
#print axioms from_B_supported
#print axioms history_support_true
#print axioms history_support_false
#print axioms all_histories_after_A
#print axioms all_histories_after_B

end AQARION.Denom5ObservedAllHistoryMarkov
