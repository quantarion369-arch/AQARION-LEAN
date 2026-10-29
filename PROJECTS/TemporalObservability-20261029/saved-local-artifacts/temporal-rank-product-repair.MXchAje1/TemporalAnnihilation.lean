import Init

set_option autoImplicit false
set_option warningAsError true

universe u v r

namespace AQARIONTemporal

/-- Observation at time t, obtained by repeated pullback along T. -/
def observeAt {X : Type u} {R : Type r}
    (T : X → X) (h : X → R) : Nat → X → R
  | 0 => h
  | t + 1 => fun x => observeAt T h t (T x)

/--
Conditional temporal-annihilation lemma.

The finite implementation must separately establish:
* pushforward/pullback duality;
* the eigenvector identity;
* homogeneity of the pairing.

No finite-sum implementation or rank conclusion is assumed proved here.
-/
theorem annihilates_all_observations
    {X : Type u} {W : Type v} {R : Type r}
    (T : X → X)
    (h : X → R)
    (pair : W → (X → R) → R)
    (push : W → W)
    (scale : R → W → W)
    (mul : R → R → R)
    (zero lambda : R)
    (w : W)
    (mul_zero : mul lambda zero = zero)
    (duality :
      ∀ g : X → R,
        pair w (fun x => g (T x)) = pair (push w) g)
    (eigen : push w = scale lambda w)
    (homogeneous :
      ∀ g : X → R,
        pair (scale lambda w) g = mul lambda (pair w g))
    (initial_zero : pair w h = zero) :
    ∀ t : Nat, pair w (observeAt T h t) = zero := by
  intro t
  induction t with
  | zero =>
      exact initial_zero
  | succ t ih =>
      change pair w (fun x => observeAt T h t (T x)) = zero
      calc
        pair w (fun x => observeAt T h t (T x))
            = pair (push w) (observeAt T h t) :=
                duality (observeAt T h t)
        _ = pair (scale lambda w) (observeAt T h t) :=
                congrArg
                  (fun weight => pair weight (observeAt T h t))
                  eigen
        _ = mul lambda (pair w (observeAt T h t)) :=
                homogeneous (observeAt T h t)
        _ = mul lambda zero :=
                congrArg (mul lambda) ih
        _ = zero := mul_zero

end AQARIONTemporal

#check AQARIONTemporal.annihilates_all_observations
#print axioms AQARIONTemporal.annihilates_all_observations
