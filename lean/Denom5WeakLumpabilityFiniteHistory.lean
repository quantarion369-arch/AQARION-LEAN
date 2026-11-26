import Denom5BalancedInitialCylinderFixed

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5WeakLumpabilityFiniteHistory

open AQARION.Denom5RationalSpan
open AQARION.Denom5CylinderProbabilityFixed
open AQARION.Denom5PitmanRogersLink
open AQARION.Denom5BalancedInitialCylinderFixed

def historyHiddenState
    (x : Vec3Q) (first : Bool) (tail : List Bool) : Vec3Q :=
  hiddenTail (balancedHiddenStart x first) tail

def historyObservedState
    (x : Vec3Q) (first : Bool) (tail : List Bool) :
    Rat × Rat :=
  observedTail (balancedObservedStart x first) tail

theorem all_finite_histories_lift
    (x : Vec3Q) (hx : balanced x)
    (first : Bool) (tail : List Bool) :
    historyHiddenState x first tail =
      liftQ (historyObservedState x first tail) := by
  exact balanced_tail_is_lift x hx first tail

theorem all_finite_history_mass_equal
    (x : Vec3Q) (hx : balanced x)
    (first : Bool) (tail : List Bool) :
    (historyHiddenState x first tail).a +
      (historyHiddenState x first tail).b +
      (historyHiddenState x first tail).c =
    (historyObservedState x first tail).1 +
      (historyObservedState x first tail).2 := by
  exact balanced_cylinder_mass_equal x hx first tail

theorem all_finite_histories_next_lift
    (x : Vec3Q) (hx : balanced x)
    (first : Bool) (tail : List Bool) (next : Bool) :
    hiddenNext (historyHiddenState x first tail) next =
      liftQ (observedNext (historyObservedState x first tail) next) := by
  rw [all_finite_histories_lift x hx first tail]
  exact hidden_next_lift next _

#print axioms all_finite_histories_lift
#print axioms all_finite_history_mass_equal
#print axioms all_finite_histories_next_lift

end AQARION.Denom5WeakLumpabilityFiniteHistory
