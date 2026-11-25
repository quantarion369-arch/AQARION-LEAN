import Mathlib
import P2Skeleton.RowTrace

set_option autoImplicit false

namespace P2Skeleton

/-- Entry `b` of a dense row, zero beyond the end. -/
def gt : List ℤ → ℕ → ℤ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, b + 1 => gt xs b

/-- Row minus `c` times the pivot row, without truncation. -/
def rowStep (c : ℤ) : List ℤ → List ℤ → List ℤ
  | [], [] => []
  | x :: xs, [] => x :: xs
  | [], y :: ys => (-(c * y)) :: rowStep c [] ys
  | x :: xs, y :: ys => (x - c * y) :: rowStep c xs ys

theorem gt_rowStep (c : ℤ) : ∀ (r p : List ℤ) (b : ℕ),
    gt (rowStep c r p) b = gt r b - c * gt p b
  | [], [], b => by simp [rowStep, gt]
  | x :: xs, [], b => by simp [rowStep, gt]
  | [], y :: ys, 0 => by simp [rowStep, gt]
  | [], y :: ys, b + 1 => by simp [rowStep, gt, gt_rowStep c [] ys b]
  | x :: xs, y :: ys, 0 => by simp [rowStep, gt]
  | x :: xs, y :: ys, b + 1 => by simp [rowStep, gt, gt_rowStep c xs ys b]

/-- Row `a` of a dense table, empty beyond the end. -/
def tgt : List (List ℤ) → ℕ → List ℤ
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, a + 1 => tgt rs a

def cell (tab : List (List ℤ)) (a b : ℕ) : ℤ := gt (tgt tab a) b

def stepAux (piv : List ℤ) (i j : ℕ) : ℕ → List (List ℤ) → List (List ℤ)
  | _, [] => []
  | k, r :: rs =>
      (if k = i then r else if gt r j = 0 then r else rowStep (gt r j * gt piv j) r piv)
        :: stepAux piv i j (k + 1) rs

/-- One elimination step on a dense table: clear column `j` from every row except row `i`. -/
def stepTab (i j : ℕ) (tab : List (List ℤ)) : List (List ℤ) :=
  stepAux (tgt tab i) i j 0 tab

theorem length_stepAux (piv : List ℤ) (i j : ℕ) :
    ∀ (rs : List (List ℤ)) (k : ℕ), (stepAux piv i j k rs).length = rs.length
  | [], k => by simp [stepAux]
  | r :: rs, k => by simp [stepAux, length_stepAux piv i j rs (k + 1)]

theorem length_stepTab (i j : ℕ) (tab : List (List ℤ)) :
    (stepTab i j tab).length = tab.length := length_stepAux _ i j tab 0

theorem tgt_stepAux (piv : List ℤ) (i j : ℕ) :
    ∀ (rs : List (List ℤ)) (k a : ℕ), a < rs.length →
      tgt (stepAux piv i j k rs) a =
        if k + a = i then tgt rs a
        else if gt (tgt rs a) j = 0 then tgt rs a
        else rowStep (gt (tgt rs a) j * gt piv j) (tgt rs a) piv
  | [], k, a, ha => by simp at ha
  | r :: rs, k, 0, _ => by
      simp only [stepAux, tgt, Nat.add_zero]
      split_ifs <;> rfl
  | r :: rs, k, a + 1, ha => by
      have ha' : a < rs.length := by simpa using ha
      have e : k + (a + 1) = (k + 1) + a := by omega
      rw [e]
      simp only [stepAux, tgt]
      exact tgt_stepAux piv i j rs (k + 1) a ha'

theorem cell_stepTab (tab : List (List ℤ)) (i j a b : ℕ) (ha : a < tab.length) :
    cell (stepTab i j tab) a b =
      if a = i then cell tab a b
      else cell tab a b - cell tab a j * cell tab i j * cell tab i b := by
  unfold cell stepTab
  rw [tgt_stepAux _ _ _ tab 0 a ha]
  by_cases h : a = i
  · simp [h]
  · by_cases h2 : gt (tgt tab a) j = 0
    · simp [h, h2]
    · simp [h, h2, gt_rowStep]

theorem gt_zero_of_forall : ∀ (r : List ℤ) (b : ℕ), (∀ x ∈ r, x = 0) → gt r b = 0
  | [], b, _ => by simp [gt]
  | x :: xs, 0, h => by simpa [gt] using h x (by simp)
  | x :: xs, b + 1, h => by
      simp only [gt]
      exact gt_zero_of_forall xs b (fun y hy => h y (by simp [hy]))

def allZeroExcept (done : List ℕ) : ℕ → List (List ℤ) → Bool
  | _, [] => true
  | k, r :: rs =>
      (decide (k ∈ done) || decide (∀ x ∈ r, x = 0)) && allZeroExcept done (k + 1) rs

theorem allZeroExcept_sound (done : List ℕ) :
    ∀ (rs : List (List ℤ)) (k : ℕ), allZeroExcept done k rs = true →
      ∀ a : ℕ, a < rs.length → k + a ∉ done → ∀ b : ℕ, gt (tgt rs a) b = 0
  | [], k, _, a, ha, _, b => by simp at ha
  | r :: rs, k, h, 0, _, hnd, b => by
      simp only [allZeroExcept, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      have hr : ∀ x ∈ r, x = 0 := by
        rcases h.1 with h1 | h1
        · exact absurd (by simpa using h1) hnd
        · exact h1
      simpa [tgt] using gt_zero_of_forall r b hr
  | r :: rs, k, h, a + 1, ha, hnd, b => by
      simp only [allZeroExcept, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      have e : k + (a + 1) = (k + 1) + a := by omega
      have ha' : a < rs.length := by simpa using ha
      have hnd' : (k + 1) + a ∉ done := by rw [← e]; exact hnd
      simpa [tgt] using allZeroExcept_sound done rs (k + 1) h.2 a ha' hnd' b

/-- Replay checker: every pivot is a plus or minus one entry in range, pivot rows are distinct,
and at the end every non-pivot row is zero. -/
def check (nc : ℕ) : List (List ℤ) → List ℕ → List (ℕ × ℕ) → Bool
  | tab, done, [] => allZeroExcept done 0 tab
  | tab, done, (i, j) :: t =>
      decide (i < tab.length) && decide (j < nc) && decide (i ∉ done) &&
        (decide (gt (tgt tab i) j = 1) || decide (gt (tgt tab i) j = -1)) &&
        check nc (stepTab i j tab) (i :: done) t

theorem check_sound (n nc : ℕ) :
    ∀ (t : List (ℕ × ℕ)) (tab : List (List ℤ)) (done : List ℕ), tab.length = n →
      check nc tab done t = true →
      ∃ t' : List (Fin n × Fin nc), t'.length = t.length ∧
        RowTrace t' (Finset.univ.filter (fun a : Fin n => a.val ∉ done))
          (fun a b => cell tab a.val b.val)
  | [], tab, done, hn, hc => by
      simp only [check] at hc
      refine ⟨[], rfl, RowTrace.nil _ _ ?_⟩
      intro a ha b
      have h2 := (Finset.mem_filter.1 ha).2
      have hlt : a.val < tab.length := by have := a.isLt; omega
      have := allZeroExcept_sound done tab 0 hc a.val hlt (by simpa using h2) b.val
      simpa [cell] using this
  | (i, j) :: t, tab, done, hn, hc => by
      simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨h1, hj⟩, hnd⟩, hu⟩, hrest⟩ := hc
      have hin : i < n := by omega
      have hlen : (stepTab i j tab).length = n := by rw [length_stepTab]; exact hn
      obtain ⟨t', hl, htr⟩ := check_sound n nc t (stepTab i j tab) (i :: done) hlen hrest
      refine ⟨(⟨i, hin⟩, ⟨j, hj⟩) :: t', by simp [hl], ?_⟩
      have hi : (⟨i, hin⟩ : Fin n) ∈ Finset.univ.filter (fun a : Fin n => a.val ∉ done) := by
        simp [Finset.mem_filter, hnd]
      have hM : pivStep (fun (a : Fin n) (b : Fin nc) => cell tab a.val b.val)
          (⟨i, hin⟩ : Fin n) (⟨j, hj⟩ : Fin nc) =
          (fun (a : Fin n) (b : Fin nc) => cell (stepTab i j tab) a.val b.val) := by
        funext a b
        have hlt : a.val < tab.length := by have := a.isLt; omega
        rw [cell_stepTab tab i j a.val b.val hlt]
        simp [pivStep, Fin.ext_iff]
      have hs : (Finset.univ.filter (fun a : Fin n => a.val ∉ done)).erase (⟨i, hin⟩ : Fin n) =
          Finset.univ.filter (fun a : Fin n => a.val ∉ (i :: done)) := by
        ext a
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
          List.mem_cons, not_or, ne_eq, Fin.ext_iff]
      refine RowTrace.cons _ _ _ _ _ hi ?_ ?_
      · simpa [cell] using hu
      · rw [hM, hs]
        exact htr

theorem rank_of_check (n nc : ℕ) (tab : List (List ℤ)) (t : List (ℕ × ℕ))
    (hn : tab.length = n) (hc : check nc tab [] t = true) (K : Type) [Field K] :
    Matrix.rank (Matrix.of fun (a : Fin n) (b : Fin nc) => ((cell tab a.val b.val : ℤ) : K))
      = t.length := by
  obtain ⟨t', hl, htr⟩ := check_sound n nc t tab [] hn hc
  have hu : (Finset.univ.filter (fun a : Fin n => a.val ∉ ([] : List ℕ))) = Finset.univ := by
    simp
  rw [hu] at htr
  rw [← hl]
  exact rank_of_rowTrace (ι := Fin n) (κ := Fin nc) K
    (fun (a : Fin n) (b : Fin nc) => cell tab a.val b.val) t' htr

end P2Skeleton

#print axioms P2Skeleton.rank_of_check
