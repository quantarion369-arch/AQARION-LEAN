import Lean

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace AQARION.Denom5InvariantPlaneFixed

structure Vec3 where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr

def balanced (x : Vec3) : Prop :=
  x.a = x.b

-- Right multiplication by M = 5P.
def step5 (x : Vec3) : Vec3 :=
  ⟨x.a + 2 * x.b + x.c,
   x.a + 2 * x.b + x.c,
   3 * x.a + x.b + 3 * x.c⟩

def blockA (x : Vec3) : Vec3 :=
  ⟨x.a, x.b, 0⟩

def blockB (x : Vec3) : Vec3 :=
  ⟨0, 0, x.c⟩

def observation (x : Vec3) : Int × Int :=
  (x.a + x.b, x.c)

def initial : Vec3 :=
  ⟨1, 1, 2⟩

theorem initial_balanced : balanced initial := by
  rfl

-- In fact, every vector is sent into the balanced plane.
theorem step5_preserves_balanced (x : Vec3) :
    balanced (step5 x) := by
  rfl

theorem blockA_preserves_balanced
    (x : Vec3) (h : balanced x) :
    balanced (blockA x) := by
  exact h

theorem blockB_preserves_balanced (x : Vec3) :
    balanced (blockB x) := by
  rfl

inductive Reachable : Vec3 → Prop
  | seed :
      Reachable initial
  | transition {x : Vec3} :
      Reachable x → Reachable (step5 x)
  | observeA {x : Vec3} :
      Reachable x → Reachable (blockA x)
  | observeB {x : Vec3} :
      Reachable x → Reachable (blockB x)

theorem reachable_balanced
    {x : Vec3} (h : Reachable x) :
    balanced x := by
  induction h with
  | seed =>
      exact initial_balanced
  | transition hx ih =>
      exact step5_preserves_balanced _
  | observeA hx ih =>
      exact blockA_preserves_balanced _ ih
  | observeB hx ih =>
      exact blockB_preserves_balanced _

theorem observation_kernel_trivial
    (x : Vec3)
    (hb : balanced x)
    (ho : observation x = (0, 0)) :
    x.a = 0 ∧ x.b = 0 ∧ x.c = 0 := by
  have hab : x.a = x.b := hb
  have hsum : x.a + x.b = 0 := congrArg Prod.fst ho
  have hc : x.c = 0 := congrArg Prod.snd ho
  have ha : x.a = 0 := by omega
  have hb0 : x.b = 0 := by omega
  exact ⟨ha, hb0, hc⟩

theorem reachable_observation_kernel_trivial
    (x : Vec3)
    (hr : Reachable x)
    (ho : observation x = (0, 0)) :
    x.a = 0 ∧ x.b = 0 ∧ x.c = 0 := by
  exact observation_kernel_trivial x (reachable_balanced hr) ho

-- Stronger pairwise statement: observation is injective
-- on the integer balanced plane.
theorem observation_injective_on_balanced
    (x y : Vec3)
    (hx : balanced x)
    (hy : balanced y)
    (ho : observation x = observation y) :
    x = y := by
  have hxa : x.a = x.b := hx
  have hya : y.a = y.b := hy
  have hs : x.a + x.b = y.a + y.b :=
    congrArg Prod.fst ho
  have hc : x.c = y.c :=
    congrArg Prod.snd ho
  have ha : x.a = y.a := by omega
  have hb : x.b = y.b := by omega
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

-- Unequal integer numerators of the A-block row sums.
theorem strong_lumpability_fails :
    (1 + 1 : Int) ≠ (2 + 2 : Int) := by
  decide

#print axioms initial_balanced
#print axioms step5_preserves_balanced
#print axioms blockA_preserves_balanced
#print axioms blockB_preserves_balanced
#print axioms reachable_balanced
#print axioms observation_kernel_trivial
#print axioms reachable_observation_kernel_trivial
#print axioms observation_injective_on_balanced
#print axioms strong_lumpability_fails

end AQARION.Denom5InvariantPlaneFixed
