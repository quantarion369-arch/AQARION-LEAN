import Denom5KernelCriterionFixed

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5SpanClosure

open AQARION.Denom5RationalSpan

theorem vec_ext
    (x y : Vec3Q)
    (ha : x.a = y.a)
    (hb : x.b = y.b)
    (hc : x.c = y.c) :
    x = y := by
  cases x with
  | mk a b c =>
      cases y with
      | mk d e f =>
          change a = d at ha
          change b = e at hb
          change c = f at hc
          cases ha
          cases hb
          cases hc
          rfl

theorem stepP_add (x y : Vec3Q) :
    stepP (add x y) = add (stepP x) (stepP y) := by
  apply vec_ext
  all_goals
    simp only [stepP, step5, scale, add]
    grind

theorem stepP_scale (r : Rat) (x : Vec3Q) :
    stepP (scale r x) = scale r (stepP x) := by
  apply vec_ext
  all_goals
    simp only [stepP, step5, scale]
    grind

theorem blockA_zero :
    blockA zero = zero := by
  rfl

theorem blockA_add (x y : Vec3Q) :
    blockA (add x y) = add (blockA x) (blockA y) := by
  simp only [blockA, add, Rat.add_zero]

theorem blockA_scale (r : Rat) (x : Vec3Q) :
    blockA (scale r x) = scale r (blockA x) := by
  simp only [blockA, scale, Rat.mul_zero]

theorem blockB_zero :
    blockB zero = zero := by
  rfl

theorem blockB_add (x y : Vec3Q) :
    blockB (add x y) = add (blockB x) (blockB y) := by
  simp only [blockB, add, Rat.add_zero]

theorem blockB_scale (r : Rat) (x : Vec3Q) :
    blockB (scale r x) = scale r (blockB x) := by
  simp only [blockB, scale, Rat.mul_zero]

-- Lift preservation of the word generators to preservation
-- of every finite rational linear combination.
theorem span_closed_of_linear_word_map
    (T : Vec3Q → Vec3Q)
    (hzero : T zero = zero)
    (hadd : ∀ x y, T (add x y) = add (T x) (T y))
    (hscale : ∀ r x, T (scale r x) = scale r (T x))
    (hword : ∀ x, WordVector x → WordVector (T x))
    {x : Vec3Q}
    (hx : InSpan x) :
    InSpan (T x) := by
  induction hx with
  | word hw =>
      exact InSpan.word (hword _ hw)
  | zero =>
      rw [hzero]
      exact InSpan.zero
  | add hx hy ihx ihy =>
      rw [hadd]
      exact InSpan.add ihx ihy
  | scale r hx ih =>
      rw [hscale]
      exact InSpan.scale r ih

theorem span_stepP_closed
    {x : Vec3Q} (hx : InSpan x) :
    InSpan (stepP x) := by
  exact span_closed_of_linear_word_map
    stepP
    AQARION.Denom5KernelCriterion.stepP_zero
    stepP_add
    stepP_scale
    (fun _ hw => WordVector.transition hw)
    hx

theorem span_blockA_closed
    {x : Vec3Q} (hx : InSpan x) :
    InSpan (blockA x) := by
  exact span_closed_of_linear_word_map
    blockA
    blockA_zero
    blockA_add
    blockA_scale
    (fun _ hw => WordVector.observeA hw)
    hx

theorem span_blockB_closed
    {x : Vec3Q} (hx : InSpan x) :
    InSpan (blockB x) := by
  exact span_closed_of_linear_word_map
    blockB
    blockB_zero
    blockB_add
    blockB_scale
    (fun _ hw => WordVector.observeB hw)
    hx

theorem span_operator_closure
    {x : Vec3Q} (hx : InSpan x) :
    InSpan (stepP x) ∧
    InSpan (blockA x) ∧
    InSpan (blockB x) := by
  exact ⟨span_stepP_closed hx,
    span_blockA_closed hx,
    span_blockB_closed hx⟩

-- Closure and the previously certified kernel condition.
-- This theorem is algebraic; it does not construct a
-- probability space or assert a general lumpability theorem.
theorem structural_certificate :
    (∀ x, InSpan x →
      InSpan (stepP x) ∧
      InSpan (blockA x) ∧
      InSpan (blockB x)) ∧
    (∀ x, InSpan x →
      observation x = (0, 0) →
      observation (stepP x) = (0, 0)) := by
  constructor
  · intro x hx
    exact span_operator_closure hx
  · intro x hx hv
    exact
      AQARION.Denom5KernelCriterion.span_kernel_transition_condition
        x hx hv

#print axioms vec_ext
#print axioms stepP_add
#print axioms stepP_scale
#print axioms blockA_zero
#print axioms blockA_add
#print axioms blockA_scale
#print axioms blockB_zero
#print axioms blockB_add
#print axioms blockB_scale
#print axioms span_closed_of_linear_word_map
#print axioms span_stepP_closed
#print axioms span_blockA_closed
#print axioms span_blockB_closed
#print axioms span_operator_closure
#print axioms structural_certificate

end AQARION.Denom5SpanClosure
