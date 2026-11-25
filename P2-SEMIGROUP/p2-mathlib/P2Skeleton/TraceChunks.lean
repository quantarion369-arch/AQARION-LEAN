import Mathlib
import P2Skeleton.TraceCheckerS

set_option autoImplicit false

namespace P2Skeleton

def chunkOk (nc : ℕ) (tab : List (List (ℕ × ℤ))) (done : List ℕ) (i j : ℕ) : Bool :=
  decide (i < tab.length) && decide (j < nc) && decide (i ∉ done) &&
    (decide (sg (tgtS tab i) j = 1) || decide (sg (tgtS tab i) j = -1))

theorem checkS_cons (nc : ℕ) (tab : List (List (ℕ × ℤ))) (done : List ℕ) (i j : ℕ)
    (t : List (ℕ × ℕ)) :
    checkS nc tab done ((i, j) :: t) =
      (chunkOk nc tab done i j && checkS nc (stepTabS i j tab) (i :: done) t) := by
  first
    | rfl
    | simp [checkS, chunkOk, Bool.and_assoc]

def chunkRun (nc : ℕ) :
    List (List (ℕ × ℤ)) → List ℕ → List (ℕ × ℕ) →
      Option (List (List (ℕ × ℤ)) × List ℕ)
  | tab, done, [] => some (tab, done)
  | tab, done, (i, j) :: t =>
      if chunkOk nc tab done i j = true then chunkRun nc (stepTabS i j tab) (i :: done) t
      else none

theorem checkS_chunk (nc : ℕ) : ∀ (c : List (ℕ × ℕ)) (tab : List (List (ℕ × ℤ)))
    (done : List ℕ) (tab' : List (List (ℕ × ℤ))) (done' : List ℕ) (rest : List (ℕ × ℕ)),
    chunkRun nc tab done c = some (tab', done') →
    checkS nc tab done (c ++ rest) = checkS nc tab' done' rest
  | [], tab, done, tab', done', rest, h => by
      simp only [chunkRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      simp
  | (i, j) :: c, tab, done, tab', done', rest, h => by
      by_cases hok : chunkOk nc tab done i j = true
      · have h2 : chunkRun nc (stepTabS i j tab) (i :: done) c = some (tab', done') := by
          simpa [chunkRun, hok] using h
        rw [List.cons_append, checkS_cons, hok, Bool.true_and]
        exact checkS_chunk nc c _ _ _ _ rest h2
      · simp [chunkRun, hok] at h

theorem checkS_finish (nc : ℕ) (c : List (ℕ × ℕ)) (tab : List (List (ℕ × ℤ)))
    (done : List ℕ) (tab' : List (List (ℕ × ℤ))) (done' : List ℕ)
    (h : chunkRun nc tab done c = some (tab', done'))
    (hz : allZeroExceptS done' 0 tab' = true) :
    checkS nc tab done c = true := by
  have e := checkS_chunk nc c tab done tab' done' [] h
  rw [List.append_nil] at e
  rw [e]
  simpa [checkS] using hz

end P2Skeleton

#print axioms P2Skeleton.checkS_chunk
#print axioms P2Skeleton.checkS_finish
