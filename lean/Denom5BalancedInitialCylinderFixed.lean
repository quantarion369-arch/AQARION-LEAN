
import Denom5PitmanRogersLink

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5BalancedInitialCylinderFixed

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure
open AQARION.Denom5ExplicitObserved
open AQARION.Denom5CylinderProbabilityFixed
open AQARION.Denom5PitmanRogersLink

def balancedHiddenStart (x : Vec3Q) (b : Bool) : Vec3Q :=
  if b then blockA x else blockB x

def balancedObservedStart (x : Vec3Q) (b : Bool) : Rat × Rat :=
  if b then observedBlockA (observation x)
  else observedBlockB (observation x)

/--
A balanced hidden vector is reconstructed from its observation.
The proof applies reconstruction only to the hidden-side block.
-/
theorem balanced_start_is_lift
    (x : Vec3Q) (hx : balanced x) (b : Bool) :
    balancedHiddenStart x b =
      liftQ (balancedObservedStart x b) := by
  have hx' : x = liftQ (observation x) :=
    (lift_observation_of_balanced x hx).symm
  cases b
  · change blockB x = liftQ (observedBlockB (observation x))
    calc
      blockB x = blockB (liftQ (observation x)) :=
        congrArg blockB hx'
      _ = liftQ (observedBlockB (observation x)) :=
        blockB_lift _
  · change blockA x = liftQ (observedBlockA (observation x))
    calc
      blockA x = blockA (liftQ (observation x)) :=
        congrArg blockA hx'
      _ = liftQ (observedBlockA (observation x)) :=
        blockA_lift _

/-- Every finite observed tail remains the lift of the hidden tail. -/
theorem balanced_tail_is_lift
    (x : Vec3Q) (hx : balanced x) (b : Bool)
    (tail : List Bool) :
    hiddenTail (balancedHiddenStart x b) tail =
      liftQ (observedTail (balancedObservedStart x b) tail) := by
  rw [balanced_start_is_lift x hx b]
  exact hidden_tail_lift tail _

/--
Exact terminal-mass equality for every finite history
from an arbitrary balanced rational initial vector.
-/
theorem balanced_cylinder_mass_equal
    (x : Vec3Q) (hx : balanced x) (b : Bool)
    (tail : List Bool) :
    (hiddenTail (balancedHiddenStart x b) tail).a +
      (hiddenTail (balancedHiddenStart x b) tail).b +
      (hiddenTail (balancedHiddenStart x b) tail).c =
    (observedTail (balancedObservedStart x b) tail).1 +
      (observedTail (balancedObservedStart x b) tail).2 := by
  rw [balanced_tail_is_lift x hx b tail]
  exact lift_mass _

#print axioms balanced_start_is_lift
#print axioms balanced_tail_is_lift
#print axioms balanced_cylinder_mass_equal

end AQARION.Denom5BalancedInitialCylinderFixed

