import Denom5RationalSpan

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5WeakLumpabilityAlgebra

open AQARION.Denom5RationalSpan

def blockAMass (x : Vec3Q) : Rat :=
  (blockA x).a + (blockA x).b

def firstAAfterA (x : Vec3Q) : Rat :=
  blockAMass (stepP (blockA x))

theorem firstAAfterA_scaled (x : Vec3Q) :
    5 * firstAAfterA x = 2 * x.a + 4 * x.b := by
  simp only [
    firstAAfterA,
    blockAMass,
    blockA,
    stepP,
    scale,
    step5
  ]
  grind

theorem firstA_three_fifths_crossmul_iff_balanced
    (x : Vec3Q) :
    5 * firstAAfterA x =
      3 * blockAMass x ↔ balanced x := by
  constructor
  · intro h
    have h' :
        2 * x.a + 4 * x.b =
          3 * (x.a + x.b) := by
      rw [firstAAfterA_scaled] at h
      simpa [blockAMass, blockA] using h
    change x.a = x.b
    grind
  · intro hb
    have hab : x.a = x.b := hb
    rw [firstAAfterA_scaled]
    simp only [blockAMass, blockA]
    grind

theorem hidden_state_after_A_is_balanced
    (x : Vec3Q) :
    balanced (blockA (stepP x)) := by
  exact blockA_balanced _ (stepP_balanced x)

theorem balanced_A_conditioning
    (x : Vec3Q) (hx : balanced x) :
    balanced (blockA x) := by
  exact blockA_balanced x hx

theorem balanced_B_conditioning
    (x : Vec3Q) :
    balanced (blockB x) := by
  exact blockB_balanced x

#print axioms firstAAfterA_scaled
#print axioms firstA_three_fifths_crossmul_iff_balanced
#print axioms hidden_state_after_A_is_balanced
#print axioms balanced_A_conditioning
#print axioms balanced_B_conditioning

end AQARION.Denom5WeakLumpabilityAlgebra
