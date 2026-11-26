import Denom5WeakLumpabilityTwoStep
import Denom5BalancedAllHistoryMarkov

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5WeakLumpabilityCapstone

open AQARION.Denom5RationalSpan
open AQARION.Denom5WeakLumpabilityTwoStep
open AQARION.Denom5BalancedAllHistoryMarkov

abbrev HiddenMassMarkov (x : Vec3Q) : Prop :=
  ∀ (first : Bool) (w : List Bool),
    (5 * hiddenHistMass x first ((w ++ [true]) ++ [true]) =
        3 * hiddenHistMass x first (w ++ [true]) ∧
      5 * hiddenHistMass x first ((w ++ [true]) ++ [false]) =
        2 * hiddenHistMass x first (w ++ [true])) ∧
    (5 * hiddenHistMass x first ((w ++ [false]) ++ [true]) =
        2 * hiddenHistMass x first (w ++ [false]) ∧
      5 * hiddenHistMass x first ((w ++ [false]) ++ [false]) =
        3 * hiddenHistMass x first (w ++ [false]))

theorem balanced_gives_hidden_mass_markov
    (x : Vec3Q) (hx : balanced x) : HiddenMassMarkov x :=
  fun first w =>
    ⟨balanced_hidden_after_A x hx first w,
     balanced_hidden_after_B x hx first w⟩

theorem weak_lumpability_mass_classification
    (x : Vec3Q) (ha : 0 ≤ x.a) (hb : 0 ≤ x.b) (hc : 0 ≤ x.c)
    (hpos : 0 < x.a + x.b + x.c) :
    (HomogeneousAA2 x ↔ balanced x) ∧
    (balanced x → HiddenMassMarkov x) :=
  ⟨homogeneousAA2_iff_balanced x ha hb hc hpos,
   balanced_gives_hidden_mass_markov x⟩

theorem stationary_hidden_mass_markov : HiddenMassMarkov initial :=
  balanced_gives_hidden_mass_markov initial initial_balanced

#print axioms balanced_gives_hidden_mass_markov
#print axioms weak_lumpability_mass_classification
#print axioms stationary_hidden_mass_markov

end AQARION.Denom5WeakLumpabilityCapstone
