import Denom5WeakLumpabilityAlgebra

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5WeakLumpabilityProbability

open AQARION.Denom5RationalSpan
open AQARION.Denom5WeakLumpabilityAlgebra

def IsProb (x : Vec3Q) : Prop :=
  0 ≤ x.a ∧ 0 ≤ x.b ∧ 0 ≤ x.c ∧ x.a + x.b + x.c = 1

theorem zero_A_mass_forces_zero
    (x : Vec3Q) (h : IsProb x) (hm : blockAMass x = 0) :
    x.a = 0 ∧ x.b = 0 := by
  obtain ⟨ha, hb, hc, hs⟩ := h
  simp only [blockAMass, blockA] at hm
  constructor <;> grind

theorem balanced_prob_components
    (x : Vec3Q) (h : IsProb x) (hb : balanced x) :
    x.b = x.a ∧ x.c = 1 - 2 * x.a ∧ 0 ≤ x.a ∧ x.a ≤ 1 / 2 := by
  obtain ⟨ha, hb', hc, hs⟩ := h
  have hab : x.a = x.b := hb
  refine ⟨?_, ?_, ha, ?_⟩ <;> grind

theorem balanced_family_is_prob (t : Rat)
    (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    IsProb (⟨t, t, 1 - 2 * t⟩ : Vec3Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> grind

theorem balanced_family_balanced (t : Rat) :
    balanced (⟨t, t, 1 - 2 * t⟩ : Vec3Q) := by
  rfl

#print axioms zero_A_mass_forces_zero
#print axioms balanced_prob_components
#print axioms balanced_family_is_prob
#print axioms balanced_family_balanced

end AQARION.Denom5WeakLumpabilityProbability
