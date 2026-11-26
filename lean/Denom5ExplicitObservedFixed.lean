import Denom5ObservableDynamics

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace AQARION.Denom5ExplicitObserved

open AQARION.Denom5RationalSpan
open AQARION.Denom5SpanClosure
open AQARION.Denom5SpanMinimality

-- Row-vector multiplication by the explicit observed matrix:
-- [[3/5, 2/5],
--  [2/5, 3/5]].
def observedStep (y : Rat × Rat) : Rat × Rat :=
  ((3 / 5 : Rat) * y.1 + (2 / 5 : Rat) * y.2,
   (2 / 5 : Rat) * y.1 + (3 / 5 : Rat) * y.2)

def observedBlockA (y : Rat × Rat) : Rat × Rat :=
  (y.1, 0)

def observedBlockB (y : Rat × Rat) : Rat × Rat :=
  (0, y.2)

-- Explicit intertwining on the entire balanced plane,
-- not merely on individual word vectors.
theorem transition_intertwining_balanced
    (x : Vec3Q)
    (hx : balanced x) :
    observation (stepP x) =
      observedStep (observation x) := by
  have hab : x.a = x.b := hx
  apply Prod.ext
  all_goals
    simp only [observation, stepP, step5, scale, observedStep]
    grind

theorem transition_intertwining_span
    (x : Vec3Q)
    (hx : InSpan x) :
    observation (stepP x) =
      observedStep (observation x) := by
  exact transition_intertwining_balanced x (span_balanced hx)

-- Projector intertwining holds for every rational vector.
theorem blockA_intertwining (x : Vec3Q) :
    observation (blockA x) =
      observedBlockA (observation x) := by
  rfl

theorem blockB_intertwining (x : Vec3Q) :
    observation (blockB x) =
      observedBlockB (observation x) := by
  simp only [observation, blockB, observedBlockB, Rat.add_zero]

-- Every vector decomposes into its two block projections.
theorem block_decomposition (x : Vec3Q) :
    add (blockA x) (blockB x) = x := by
  apply vec_ext
  · simp only [add, blockA, blockB, Rat.add_zero]
  · simp only [add, blockA, blockB, Rat.add_zero]
  · simp only [add, blockA, blockB, Rat.zero_add]

-- For predicates closed under addition and both projectors,
-- the initial seed and the pair of projected seeds are equivalent.
theorem initial_seed_iff_block_seeds
    (S : Vec3Q → Prop)
    (hsub : IsRationalSubspace S)
    (hinv : IsOperatorInvariant S) :
    S initial ↔
      S (blockA initial) ∧ S (blockB initial) := by
  rcases hsub with ⟨hzero, hadd, hscale⟩
  rcases hinv with ⟨hstep, hA, hB⟩
  constructor
  · intro hseed
    exact ⟨hA _ hseed, hB _ hseed⟩
  · intro hseeds
    have hsum :
        S (add (blockA initial) (blockB initial)) :=
      hadd _ _ hseeds.1 hseeds.2
    rw [block_decomposition] at hsum
    exact hsum

-- Minimality with block-projected initial vectors as seeds.
theorem span_minimal_from_block_seeds
    (S : Vec3Q → Prop)
    (hA : S (blockA initial))
    (hB : S (blockB initial))
    (hsub : IsRationalSubspace S)
    (hinv : IsOperatorInvariant S) :
    ∀ {x : Vec3Q}, InSpan x → S x := by
  have hseed : S initial :=
    (initial_seed_iff_block_seeds S hsub hinv).mpr ⟨hA, hB⟩
  intro x hx
  exact span_minimal S hseed hsub hinv hx

theorem span_contains_block_seeds :
    InSpan (blockA initial) ∧
    InSpan (blockB initial) := by
  exact ⟨
    span_blockA_closed span_contains_initial,
    span_blockB_closed span_contains_initial
  ⟩

-- The explicit observed initial distribution.
theorem observed_initial :
    observation initial = ((1 / 2 : Rat), (1 / 2 : Rat)) := by
  apply Prod.ext <;> simp only [observation, initial] <;> grind

#print axioms transition_intertwining_balanced
#print axioms transition_intertwining_span
#print axioms blockA_intertwining
#print axioms blockB_intertwining
#print axioms block_decomposition
#print axioms initial_seed_iff_block_seeds
#print axioms span_minimal_from_block_seeds
#print axioms span_contains_block_seeds
#print axioms observed_initial

end AQARION.Denom5ExplicitObserved
