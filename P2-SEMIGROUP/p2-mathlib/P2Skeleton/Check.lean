import Mathlib
import P2Skeleton.RowTrace

set_option autoImplicit false

namespace P2Skeleton

/-- Indexed map with an explicit counter, so `getD` lemmas can be proved by induction. -/
def mapIdxFrom {α β : Type} (f : ℕ → α → β) : ℕ → List α → List β
  | _, [] => []
  | n, x :: xs => f n x :: mapIdxFrom f (n + 1) xs

def mapIdxList {α β : Type} (f : ℕ → α → β) (l : List α) : List β :=
  mapIdxFrom f 0 l

theorem length_mapIdxFrom {α β : Type} (f : ℕ → α → β) (n : ℕ) (l : List α) :
    (mapIdxFrom f n l).length = l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [mapIdxFrom, ih]

theorem getD_mapIdxFrom {α β : Type} [Inhabited α] (f : ℕ → α → β) (n : ℕ) (l : List α) (k : ℕ) (d : β) :
    (mapIdxFrom f n l).getD k d =
      if h : k < l.length then f (n + k) (l.getD k default) else d := by
  induction l generalizing n k with
  | nil => simp [mapIdxFrom]
  | cons x xs ih =>
    cases k with
    | zero => simp [mapIdxFrom]
    | succ k =>
      have e1 : (mapIdxFrom f n (x :: xs)).getD (k + 1) d =
          (mapIdxFrom f (n + 1) xs).getD k d := rfl
      rw [e1, ih]
      by_cases hk : k < xs.length
      · have h2 : k + 1 < (x :: xs).length := by simp [hk]
        simp [h2, hk, Nat.add_assoc, List.getD_cons_succ]
      · have h2 : ¬ (k + 1 < (x :: xs).length) := by simp [hk]
        simp [h2, hk]

/-- Table as a function on `Fin` indices, via `getD` with zero default. -/
def tableMat {m n : ℕ} (T : List (List ℤ)) : Fin m → Fin n → ℤ :=
  fun a b => (T.getD a.val []).getD b.val 0

/-- One elimination step on tables. The pivot row is left unchanged, to match `pivStep`. -/
def stepTable (T : List (List ℤ)) (p : ℕ × ℕ) : List (List ℤ) :=
  let i := p.1
  let j := p.2
  let piv := T.getD i []
  let u := piv.getD j 0
  mapIdxList (fun r row =>
    if r = i then row
    else mapIdxList (fun b x => x - (row.getD j 0 * u) * piv.getD b 0) row) T

/-- The table stepper equals `pivStep` on functions. Draft: proof to be filled next. -/
theorem tableMat_step {m n : ℕ} (T : List (List ℤ)) (hT : T.length = m)
    (hrows : ∀ row ∈ T, row.length = n) (i : Fin m) (j : Fin n) :
    tableMat (stepTable T (i.val, j.val)) = pivStep (tableMat T) i j := by
  sorry

end P2Skeleton

#print axioms P2Skeleton.getD_mapIdxFrom
#print axioms P2Skeleton.tableMat_step
