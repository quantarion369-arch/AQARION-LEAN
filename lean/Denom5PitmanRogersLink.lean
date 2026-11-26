import Denom5CylinderProbabilityFixed

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5PitmanRogersLink

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure
open AQARION.Denom5ExplicitObserved
open AQARION.Denom5CylinderProbabilityFixed

def liftQ (y : Rat × Rat) : Vec3Q :=
  ⟨y.1 / 2, y.1 / 2, y.2⟩

theorem lift_balanced (y : Rat × Rat) : balanced (liftQ y) := by
  rfl

theorem observation_lift (y : Rat × Rat) :
    observation (liftQ y) = y := by
  apply Prod.ext <;> simp only [observation, liftQ] <;> grind

theorem lift_observation_of_balanced
    (x : Vec3Q) (hx : balanced x) :
    liftQ (observation x) = x := by
  have hab : x.a = x.b := hx
  apply vec_ext <;> simp only [liftQ, observation] <;> grind

theorem stepP_lift (y : Rat × Rat) :
    stepP (liftQ y) = liftQ (observedStep y) := by
  apply vec_ext <;>
    simp only [stepP, step5, scale, liftQ, observedStep] <;> grind

theorem blockA_lift (y : Rat × Rat) :
    blockA (liftQ y) = liftQ (observedBlockA y) := by
  apply vec_ext <;> simp only [blockA, liftQ, observedBlockA]

theorem blockB_lift (y : Rat × Rat) :
    blockB (liftQ y) = liftQ (observedBlockB y) := by
  apply vec_ext <;> simp only [blockB, liftQ, observedBlockB] <;> grind

theorem lift_mass (y : Rat × Rat) :
    (liftQ y).a + (liftQ y).b + (liftQ y).c = y.1 + y.2 := by
  simp only [liftQ]
  grind

theorem hidden_next_lift (b : Bool) (y : Rat × Rat) :
    hiddenNext (liftQ y) b = liftQ (observedNext y b) := by
  cases b
  · change blockB (stepP (liftQ y)) =
      liftQ (observedBlockB (observedStep y))
    rw [stepP_lift, blockB_lift]
  · change blockA (stepP (liftQ y)) =
      liftQ (observedBlockA (observedStep y))
    rw [stepP_lift, blockA_lift]

theorem hidden_tail_lift (tail : List Bool) :
    ∀ y : Rat × Rat,
      hiddenTail (liftQ y) tail = liftQ (observedTail y tail) := by
  induction tail with
  | nil =>
      intro y
      rfl
  | cons b bs ih =>
      intro y
      change hiddenTail (hiddenNext (liftQ y) b) bs =
        liftQ (observedTail (observedNext y b) bs)
      rw [hidden_next_lift b y]
      exact ih _

theorem hidden_start_lift (b : Bool) :
    hiddenStart b = liftQ (observedStart b) := by
  cases b
  · change blockB initial = liftQ (observedBlockB (observation initial))
    rw [← blockB_lift,
      lift_observation_of_balanced initial initial_balanced]
  · change blockA initial = liftQ (observedBlockA (observation initial))
    rw [← blockA_lift,
      lift_observation_of_balanced initial initial_balanced]

theorem hidden_cylinder_is_lift (b : Bool) (tail : List Bool) :
    hiddenTail (hiddenStart b) tail =
      liftQ (observedTail (observedStart b) tail) := by
  rw [hidden_start_lift]
  exact hidden_tail_lift tail _

#print axioms lift_balanced
#print axioms observation_lift
#print axioms lift_observation_of_balanced
#print axioms stepP_lift
#print axioms blockA_lift
#print axioms blockB_lift
#print axioms lift_mass
#print axioms hidden_next_lift
#print axioms hidden_tail_lift
#print axioms hidden_start_lift
#print axioms hidden_cylinder_is_lift

end AQARION.Denom5PitmanRogersLink
