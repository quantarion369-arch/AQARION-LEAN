import Denom5SpanClosure

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5SpanMinimality

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure

/-
A candidate rational subspace is represented by a predicate.
These hypotheses express containment of zero and closure
under rational addition and scalar multiplication.
-/
def IsRationalSubspace (S : Vec3Q → Prop) : Prop :=
  S zero ∧
  (∀ x y, S x → S y → S (add x y)) ∧
  (∀ r x, S x → S (scale r x))

/-
Operator invariance under the three operations used to
generate the AQARION finite-word family.
-/
def IsOperatorInvariant (S : Vec3Q → Prop) : Prop :=
  (∀ x, S x → S (stepP x)) ∧
  (∀ x, S x → S (blockA x)) ∧
  (∀ x, S x → S (blockB x))

/-
Every operator-word vector belongs to any invariant
predicate containing the initial vector.
-/
theorem word_vectors_in_every_invariant
    (S : Vec3Q → Prop)
    (hseed : S initial)
    (hinv : IsOperatorInvariant S)
    {x : Vec3Q}
    (hx : WordVector x) :
    S x := by
  rcases hinv with ⟨hstep, hA, hB⟩
  induction hx with
  | seed =>
      exact hseed
  | transition hw ih =>
      exact hstep _ ih
  | observeA hw ih =>
      exact hA _ ih
  | observeB hw ih =>
      exact hB _ ih

/-
Least-subspace property:
every rational subspace containing the seed and invariant
under the three operators contains the generated span.
-/
theorem span_minimal
    (S : Vec3Q → Prop)
    (hseed : S initial)
    (hsub : IsRationalSubspace S)
    (hinv : IsOperatorInvariant S) :
    ∀ {x : Vec3Q}, InSpan x → S x := by
  rcases hsub with ⟨hzero, hadd, hscale⟩
  intro x hx
  induction hx with
  | word hw =>
      exact word_vectors_in_every_invariant
        S hseed hinv hw
  | zero =>
      exact hzero
  | add hx hy ihx ihy =>
      exact hadd _ _ ihx ihy
  | scale r hx ih =>
      exact hscale r _ ih

/-
The generated span contains its own seed.
-/
theorem span_contains_initial :
    InSpan initial :=
  InSpan.word WordVector.seed

/-
The generated span is a rational subspace.
-/
theorem span_is_rational_subspace :
    IsRationalSubspace InSpan := by
  constructor
  · exact InSpan.zero
  constructor
  · intro x y hx hy
    exact InSpan.add hx hy
  · intro r x hx
    exact InSpan.scale r hx

/-
The generated span is invariant under transition and
both block-observation operators.
-/
theorem span_is_operator_invariant :
    IsOperatorInvariant InSpan := by
  constructor
  · intro x hx
    exact span_stepP_closed hx
  constructor
  · intro x hx
    exact span_blockA_closed hx
  · intro x hx
    exact span_blockB_closed hx

/-
Combined minimality certificate:
  1. the generated span contains the seed;
  2. it is a rational subspace;
  3. it is operator invariant;
  4. it is contained in every other subspace with
     those same properties.
-/
theorem generated_span_is_least :
    InSpan initial ∧
    IsRationalSubspace InSpan ∧
    IsOperatorInvariant InSpan ∧
    (∀ S : Vec3Q → Prop,
      S initial →
      IsRationalSubspace S →
      IsOperatorInvariant S →
      ∀ {x : Vec3Q}, InSpan x → S x) := by
  refine ⟨span_contains_initial,
    span_is_rational_subspace,
    span_is_operator_invariant,
    ?_⟩
  intro S hseed hsub hinv x hx
  exact span_minimal S hseed hsub hinv hx

#print axioms word_vectors_in_every_invariant
#print axioms span_minimal
#print axioms span_contains_initial
#print axioms span_is_rational_subspace
#print axioms span_is_operator_invariant
#print axioms generated_span_is_least

end AQARION.Denom5SpanMinimality
