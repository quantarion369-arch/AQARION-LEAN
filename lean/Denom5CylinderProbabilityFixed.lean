import Denom5FiniteWordSimulationCore2

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5CylinderProbabilityFixed

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure
open AQARION.Denom5ExplicitObserved
open AQARION.Denom5FiniteWordSimulationCore2

/-
true  = block A = {0,1}
false = block B = {2}
-/

def hiddenStart (b : Bool) : Vec3Q :=
  if b then blockA initial else blockB initial

def observedStart (b : Bool) : Rat × Rat :=
  if b then
    observedBlockA (observation initial)
  else
    observedBlockB (observation initial)

def hiddenNext (x : Vec3Q) (b : Bool) : Vec3Q :=
  if b then blockA (stepP x) else blockB (stepP x)

def observedNext (y : Rat × Rat) (b : Bool) : Rat × Rat :=
  if b then observedBlockA (observedStep y)
  else observedBlockB (observedStep y)

def hiddenTail (x : Vec3Q) : List Bool → Vec3Q
  | [] => x
  | b :: bs => hiddenTail (hiddenNext x b) bs

def observedTail (y : Rat × Rat) : List Bool → Rat × Rat
  | [] => y
  | b :: bs => observedTail (observedNext y b) bs

theorem hidden_start_in_span (b : Bool) :
    InSpan (hiddenStart b) := by
  cases b
  · exact span_blockB_closed (InSpan.word WordVector.seed)
  · exact span_blockA_closed (InSpan.word WordVector.seed)

theorem hidden_next_in_span
    (b : Bool) {x : Vec3Q}
    (hx : InSpan x) :
    InSpan (hiddenNext x b) := by
  cases b
  · exact span_blockB_closed (span_stepP_closed hx)
  · exact span_blockA_closed (span_stepP_closed hx)

theorem hidden_tail_in_span
    (tail : List Bool) :
    ∀ x : Vec3Q, InSpan x →
      InSpan (hiddenTail x tail) := by
  induction tail with
  | nil =>
      intro x hx
      exact hx
  | cons b bs ih =>
      intro x hx
      exact ih (hiddenNext x b)
        (hidden_next_in_span b hx)

theorem hidden_next_intertwining
    (b : Bool) (x : Vec3Q)
    (hx : InSpan x) :
    observation (hiddenNext x b) =
      observedNext (observation x) b := by
  cases b
  · change
      observation (blockB (stepP x)) =
        observedBlockB (observedStep (observation x))
    rw [blockB_intertwining]
    rw [transition_intertwining_span x hx]
  · change
      observation (blockA (stepP x)) =
        observedBlockA (observedStep (observation x))
    rw [blockA_intertwining]
    rw [transition_intertwining_span x hx]

/-
Corrected induction direction:
replace observedNext by observation(hiddenNext),
then apply the induction hypothesis.
-/

theorem hidden_tail_intertwining
    (tail : List Bool) :
    ∀ x : Vec3Q, InSpan x →
      observation (hiddenTail x tail) =
        observedTail (observation x) tail := by
  induction tail with
  | nil =>
      intro x hx
      rfl
  | cons b bs ih =>
      intro x hx
      change
        observation (hiddenTail (hiddenNext x b) bs) =
        observedTail (observedNext (observation x) b) bs
      have hstep :
          observation (hiddenNext x b) =
            observedNext (observation x) b :=
        hidden_next_intertwining b x hx
      rw [← hstep]
      exact ih (hiddenNext x b)
        (hidden_next_in_span b hx)

theorem hidden_start_intertwining (b : Bool) :
    observation (hiddenStart b) = observedStart b := by
  cases b
  · change
      observation (blockB initial) =
        observedBlockB (observation initial)
    exact blockB_intertwining initial
  · change
      observation (blockA initial) =
        observedBlockA (observation initial)
    exact blockA_intertwining initial

theorem terminal_mass_identity (x : Vec3Q) :
    x.a + x.b + x.c =
      (observation x).1 + (observation x).2 := by
  rfl

/-
Every nonempty finite history has the same hidden
and observed terminal mass.
-/

theorem cylinder_probability_equal
    (b : Bool) (tail : List Bool) :
    let x := hiddenTail (hiddenStart b) tail
    let y := observedTail (observedStart b) tail
    x.a + x.b + x.c = y.1 + y.2 := by
  dsimp
  have hx : InSpan (hiddenStart b) :=
    hidden_start_in_span b
  have hstart :
      observation (hiddenStart b) = observedStart b :=
    hidden_start_intertwining b
  have hhistory :
      observation (hiddenTail (hiddenStart b) tail) =
        observedTail (observation (hiddenStart b)) tail :=
    hidden_tail_intertwining tail (hiddenStart b) hx
  calc
    (hiddenTail (hiddenStart b) tail).a +
        (hiddenTail (hiddenStart b) tail).b +
        (hiddenTail (hiddenStart b) tail).c
        =
        (observation (hiddenTail (hiddenStart b) tail)).1 +
          (observation (hiddenTail (hiddenStart b) tail)).2 :=
          terminal_mass_identity _
    _ =
        (observedTail (observedStart b) tail).1 +
          (observedTail (observedStart b) tail).2 := by
          rw [hhistory, hstart]

theorem empty_history_mass :
    initial.a + initial.b + initial.c =
      (observation initial).1 +
        (observation initial).2 := by
  exact terminal_mass_identity initial

#print axioms hidden_start_in_span
#print axioms hidden_next_in_span
#print axioms hidden_tail_in_span
#print axioms hidden_next_intertwining
#print axioms hidden_tail_intertwining
#print axioms hidden_start_intertwining
#print axioms terminal_mass_identity
#print axioms cylinder_probability_equal
#print axioms empty_history_mass

end AQARION.Denom5CylinderProbabilityFixed
