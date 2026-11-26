import Denom5ExplicitObservedFixed

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5FiniteWordSimulationCore2

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanMinimality
open AQARION.Denom5ExplicitObserved

inductive ObservedWordVector : Rat × Rat → Prop
  | seed :
      ObservedWordVector (observation initial)
  | transition {y : Rat × Rat} :
      ObservedWordVector y →
      ObservedWordVector (observedStep y)
  | observeA {y : Rat × Rat} :
      ObservedWordVector y →
      ObservedWordVector (observedBlockA y)
  | observeB {y : Rat × Rat} :
      ObservedWordVector y →
      ObservedWordVector (observedBlockB y)

theorem word_observation_simulation
    {x : Vec3Q}
    (hx : WordVector x) :
    ∃ y : Rat × Rat,
      ObservedWordVector y ∧ observation x = y := by
  induction hx with
  | seed =>
      exact ⟨observation initial,
        ObservedWordVector.seed,
        rfl⟩
  | transition hw ih =>
      rcases ih with ⟨y, hy, hxy⟩
      refine ⟨observedStep y,
        ObservedWordVector.transition hy,
        ?_⟩
      rw [transition_intertwining_span
        _ (InSpan.word hw), hxy]
  | observeA hw ih =>
      rcases ih with ⟨y, hy, hxy⟩
      refine ⟨observedBlockA y,
        ObservedWordVector.observeA hy,
        ?_⟩
      rw [blockA_intertwining, hxy]
  | observeB hw ih =>
      rcases ih with ⟨y, hy, hxy⟩
      refine ⟨observedBlockB y,
        ObservedWordVector.observeB hy,
        ?_⟩
      rw [blockB_intertwining, hxy]

theorem word_observed_state_unique
    {x : Vec3Q}
    (hx : WordVector x)
    {y z : Rat × Rat}
    (hy : ObservedWordVector y)
    (hz : ObservedWordVector z)
    (hxy : observation x = y)
    (hxz : observation x = z) :
    y = z := by
  rw [← hxy, ← hxz]

theorem hidden_mass_eq_observed_mass
    (x : Vec3Q) :
    x.a + x.b + x.c =
      (observation x).1 + (observation x).2 := by
  rfl

theorem finite_word_mass_simulation
    {x : Vec3Q}
    (hx : WordVector x) :
    ∃ y : Rat × Rat,
      ObservedWordVector y ∧
      observation x = y ∧
      x.a + x.b + x.c = y.1 + y.2 := by
  rcases word_observation_simulation hx with
    ⟨y, hy, hxy⟩
  refine ⟨y, hy, hxy, ?_⟩
  rw [← hxy]
  exact hidden_mass_eq_observed_mass x

#print axioms word_observation_simulation
#print axioms word_observed_state_unique
#print axioms hidden_mass_eq_observed_mass
#print axioms finite_word_mass_simulation

end AQARION.Denom5FiniteWordSimulationCore2
