import Denom5SpanMinimality

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5ObservableDynamics

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure
open AQARION.Denom5SpanMinimality

/-
On the generated span, equality of observations implies
equality of the underlying vectors.
-/
theorem same_observation_same_state
    {x y : Vec3Q}
    (hx : InSpan x)
    (hy : InSpan y)
    (hobs : observation x = observation y) :
    x = y := by
  exact observation_injective_on_span x y hx hy hobs

/-
The transition has a well-defined observable output:
the result depends only on the current observation,
provided both states belong to the generated span.
-/
theorem transition_observation_respects_equality
    {x y : Vec3Q}
    (hx : InSpan x)
    (hy : InSpan y)
    (hobs : observation x = observation y) :
    observation (stepP x) = observation (stepP y) := by
  have hxy : x = y :=
    same_observation_same_state hx hy hobs
  rw [hxy]

/-
The first block projection also respects equality
of observations on the generated span.
-/
theorem blockA_observation_respects_equality
    {x y : Vec3Q}
    (hx : InSpan x)
    (hy : InSpan y)
    (hobs : observation x = observation y) :
    observation (blockA x) = observation (blockA y) := by
  have hxy : x = y :=
    same_observation_same_state hx hy hobs
  rw [hxy]

/-
The second block projection also respects equality
of observations on the generated span.
-/
theorem blockB_observation_respects_equality
    {x y : Vec3Q}
    (hx : InSpan x)
    (hy : InSpan y)
    (hobs : observation x = observation y) :
    observation (blockB x) = observation (blockB y) := by
  have hxy : x = y :=
    same_observation_same_state hx hy hobs
  rw [hxy]

/-
All three induced observable outputs are unambiguous.
-/
theorem observable_dynamics_well_defined
    {x y : Vec3Q}
    (hx : InSpan x)
    (hy : InSpan y)
    (hobs : observation x = observation y) :
    observation (stepP x) = observation (stepP y) ∧
    observation (blockA x) = observation (blockA y) ∧
    observation (blockB x) = observation (blockB y) := by
  exact ⟨
    transition_observation_respects_equality hx hy hobs,
    blockA_observation_respects_equality hx hy hobs,
    blockB_observation_respects_equality hx hy hobs
  ⟩

/-
The observation map has trivial kernel on the generated span.
-/
theorem zero_observation_forces_zero
    {x : Vec3Q}
    (hx : InSpan x)
    (hobs : observation x = (0, 0)) :
    x = zero := by
  exact span_observation_kernel_trivial x hx hobs

#print axioms same_observation_same_state
#print axioms transition_observation_respects_equality
#print axioms blockA_observation_respects_equality
#print axioms blockB_observation_respects_equality
#print axioms observable_dynamics_well_defined
#print axioms zero_observation_forces_zero

end AQARION.Denom5ObservableDynamics
