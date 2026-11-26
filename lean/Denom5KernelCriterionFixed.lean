import Denom5RationalSpan

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace AQARION.ZeroKernelBridge

-- Abstract zero-kernel sufficient condition.
-- No vector-space or probability assumptions are hidden here.
theorem kernel_transition_of_trivial_kernel
    {X O : Type}
    (S : X → Prop)
    (T : X → X)
    (V : X → O)
    (zeroX : X)
    (zeroO : O)
    (hkernel :
      ∀ x, S x → V x = zeroO → x = zeroX)
    (hzero : V (T zeroX) = zeroO) :
    ∀ x, S x → V x = zeroO → V (T x) = zeroO := by
  intro x hx hv
  have hxzero : x = zeroX := hkernel x hx hv
  rw [hxzero]
  exact hzero

end AQARION.ZeroKernelBridge

namespace AQARION.Denom5KernelCriterion

open AQARION.Denom5RationalSpan

theorem stepP_zero :
    stepP zero = zero := by
  simp only [stepP, step5, scale, zero, observation, Rat.mul_zero, Rat.add_zero]

theorem observation_zero :
    observation zero = (0, 0) := by
  simp only [stepP, step5, scale, zero, observation, Rat.mul_zero, Rat.add_zero]

theorem zero_observation_after_transition :
    observation (stepP zero) = (0, 0) := by
  rw [stepP_zero]
  exact observation_zero

-- Concrete condition:
-- every zero-observation vector in the generated rational span
-- still has zero observation after multiplication by P.
theorem span_kernel_transition_condition
    (x : Vec3Q)
    (hx : InSpan x)
    (hv : observation x = (0, 0)) :
    observation (stepP x) = (0, 0) := by
  exact
    AQARION.ZeroKernelBridge.kernel_transition_of_trivial_kernel
      InSpan
      stepP
      observation
      zero
      (0, 0)
      span_observation_kernel_trivial
      zero_observation_after_transition
      x hx hv

-- Stronger concrete consequence: the transitioned vector
-- itself is zero, not merely its observation.
theorem span_kernel_transition_is_zero
    (x : Vec3Q)
    (hx : InSpan x)
    (hv : observation x = (0, 0)) :
    stepP x = zero := by
  have hxzero : x = zero :=
    span_observation_kernel_trivial x hx hv
  rw [hxzero]
  exact stepP_zero

#print axioms AQARION.ZeroKernelBridge.kernel_transition_of_trivial_kernel
#print axioms stepP_zero
#print axioms observation_zero
#print axioms zero_observation_after_transition
#print axioms span_kernel_transition_condition
#print axioms span_kernel_transition_is_zero

end AQARION.Denom5KernelCriterion
