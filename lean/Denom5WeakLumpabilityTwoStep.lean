import Denom5WeakLumpabilityAlgebra

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5WeakLumpabilityTwoStep

open AQARION.Denom5RationalSpan
open AQARION.Denom5WeakLumpabilityAlgebra

theorem second_step_three_fifths (x : Vec3Q) :
    5 * firstAAfterA (stepP x) = 3 * blockAMass (stepP x) :=
  (firstA_three_fifths_crossmul_iff_balanced (stepP x)).2
    (stepP_balanced x)

theorem blockAMass_step_scaled (x : Vec3Q) :
    5 * blockAMass (stepP x) = 2 * (x.a + 2 * x.b + x.c) := by
  simp only [blockAMass, blockA, stepP, scale, step5]
  grind

theorem blockAMass_step_ne_zero
    (x : Vec3Q) (ha : 0 ≤ x.a) (hb : 0 ≤ x.b) (hc : 0 ≤ x.c)
    (hpos : 0 < x.a + x.b + x.c) :
    blockAMass (stepP x) ≠ 0 := by
  have h := blockAMass_step_scaled x
  intro h0
  grind

theorem rat_cancel (p01 p11 m0 m1 : Rat)
    (h2 : 5 * p11 = 3 * m1)
    (h : p01 * m1 = p11 * m0)
    (hm : m1 ≠ 0) :
    5 * p01 = 3 * m0 := by
  grind

theorem rat_converse (p01 p11 m0 m1 : Rat)
    (h1 : 5 * p01 = 3 * m0)
    (h2 : 5 * p11 = 3 * m1) :
    p01 * m1 = p11 * m0 := by
  grind

def HomogeneousAA2 (x : Vec3Q) : Prop :=
  firstAAfterA x * blockAMass (stepP x) =
    firstAAfterA (stepP x) * blockAMass x

theorem homogeneousAA2_forces_balanced
    (x : Vec3Q) (hm1 : blockAMass (stepP x) ≠ 0)
    (h : HomogeneousAA2 x) :
    balanced x := by
  have h2 := second_step_three_fifths x
  have h3 := rat_cancel (firstAAfterA x) (firstAAfterA (stepP x))
    (blockAMass x) (blockAMass (stepP x)) h2 h hm1
  exact (firstA_three_fifths_crossmul_iff_balanced x).1 h3

theorem balanced_forces_homogeneousAA2
    (x : Vec3Q) (hx : balanced x) :
    HomogeneousAA2 x := by
  have h1 := (firstA_three_fifths_crossmul_iff_balanced x).2 hx
  have h2 := second_step_three_fifths x
  exact rat_converse _ _ _ _ h1 h2

theorem homogeneousAA2_iff_balanced
    (x : Vec3Q) (ha : 0 ≤ x.a) (hb : 0 ≤ x.b) (hc : 0 ≤ x.c)
    (hpos : 0 < x.a + x.b + x.c) :
    HomogeneousAA2 x ↔ balanced x :=
  ⟨homogeneousAA2_forces_balanced x
      (blockAMass_step_ne_zero x ha hb hc hpos),
   balanced_forces_homogeneousAA2 x⟩

#print axioms second_step_three_fifths
#print axioms blockAMass_step_scaled
#print axioms blockAMass_step_ne_zero
#print axioms rat_cancel
#print axioms rat_converse
#print axioms homogeneousAA2_forces_balanced
#print axioms balanced_forces_homogeneousAA2
#print axioms homogeneousAA2_iff_balanced

end AQARION.Denom5WeakLumpabilityTwoStep
