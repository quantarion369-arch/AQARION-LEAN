import Denom5BalancedInitialCylinderFixed
import Denom5ObservedAllHistoryMarkov

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5BalancedAllHistoryMarkov

open AQARION.Denom5RationalSpan
open AQARION.Denom5CylinderProbabilityFixed
open AQARION.Denom5BalancedInitialCylinderFixed
open AQARION.Denom5ObservedAllHistoryMarkov

def hiddenHistMass (x : Vec3Q) (first : Bool) (t : List Bool) : Rat :=
  (hiddenTail (balancedHiddenStart x first) t).a +
  (hiddenTail (balancedHiddenStart x first) t).b +
  (hiddenTail (balancedHiddenStart x first) t).c

theorem hiddenHistMass_eq
    (x : Vec3Q) (hx : balanced x) (first : Bool) (t : List Bool) :
    hiddenHistMass x first t =
      histMass (observedTail (balancedObservedStart x first) t) :=
  balanced_cylinder_mass_equal x hx first t

theorem balanced_hidden_after_A
    (x : Vec3Q) (hx : balanced x) (first : Bool) (w : List Bool) :
    5 * hiddenHistMass x first ((w ++ [true]) ++ [true]) =
      3 * hiddenHistMass x first (w ++ [true]) ∧
    5 * hiddenHistMass x first ((w ++ [true]) ++ [false]) =
      2 * hiddenHistMass x first (w ++ [true]) := by
  have h := all_histories_after_A (balancedObservedStart x first) w
  obtain ⟨h1, h2⟩ := h
  have e : ∀ d : Bool,
      observedTail (balancedObservedStart x first) ((w ++ [true]) ++ [d]) =
        observedNext
          (observedTail (balancedObservedStart x first) (w ++ [true])) d :=
    fun d => observedTail_append_single (w ++ [true]) d _
  refine ⟨?_, ?_⟩
  · rw [hiddenHistMass_eq x hx first, hiddenHistMass_eq x hx first, e true]
    exact h1
  · rw [hiddenHistMass_eq x hx first, hiddenHistMass_eq x hx first, e false]
    exact h2

theorem balanced_hidden_after_B
    (x : Vec3Q) (hx : balanced x) (first : Bool) (w : List Bool) :
    5 * hiddenHistMass x first ((w ++ [false]) ++ [true]) =
      2 * hiddenHistMass x first (w ++ [false]) ∧
    5 * hiddenHistMass x first ((w ++ [false]) ++ [false]) =
      3 * hiddenHistMass x first (w ++ [false]) := by
  have h := all_histories_after_B (balancedObservedStart x first) w
  obtain ⟨h1, h2⟩ := h
  have e : ∀ d : Bool,
      observedTail (balancedObservedStart x first) ((w ++ [false]) ++ [d]) =
        observedNext
          (observedTail (balancedObservedStart x first) (w ++ [false])) d :=
    fun d => observedTail_append_single (w ++ [false]) d _
  refine ⟨?_, ?_⟩
  · rw [hiddenHistMass_eq x hx first, hiddenHistMass_eq x hx first, e true]
    exact h1
  · rw [hiddenHistMass_eq x hx first, hiddenHistMass_eq x hx first, e false]
    exact h2

#print axioms hiddenHistMass_eq
#print axioms balanced_hidden_after_A
#print axioms balanced_hidden_after_B

end AQARION.Denom5BalancedAllHistoryMarkov
