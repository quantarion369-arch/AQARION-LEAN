import Mathlib
import P2Skeleton.RowTrace

set_option autoImplicit false

namespace P2Skeleton

/-- Value of a sparse row at column `b`: the sum of all entries with that key. -/
def sg : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => 0
  | (k, v) :: r, b => (if k = b then v else 0) + sg r b

theorem sg_append (r s : List (ℕ × ℤ)) (b : ℕ) : sg (r ++ s) b = sg r b + sg s b := by
  induction r with
  | nil => simp [sg]
  | cons p r ih =>
      obtain ⟨k, v⟩ := p
      simp [sg, ih, add_assoc]

def scaleNeg (c : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => []
  | (k, w) :: p => (k, -(c * w)) :: scaleNeg c p

theorem sg_scaleNeg (c : ℤ) : ∀ (p : List (ℕ × ℤ)) (b : ℕ),
    sg (scaleNeg c p) b = -(c * sg p b)
  | [], b => by simp [scaleNeg, sg]
  | (k, w) :: p, b => by
      simp only [scaleNeg, sg, sg_scaleNeg c p b]
      split_ifs <;> ring

def addTo (k : ℕ) (v : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => [(k, v)]
  | (k', v') :: r => if k' = k then (k', v' + v) :: r else (k', v') :: addTo k v r

theorem sg_addTo (k : ℕ) (v : ℤ) : ∀ (r : List (ℕ × ℤ)) (b : ℕ),
    sg (addTo k v r) b = (if k = b then v else 0) + sg r b
  | [], b => by simp [addTo, sg]
  | (k', v') :: r, b => by
      by_cases h : k' = k
      · subst h
        by_cases hb : k' = b
        · first
            | (simp [addTo, sg, hb]; done)
            | (simp [addTo, sg, hb]; ring)
        · simp [addTo, sg, hb]
      · simp only [addTo, if_neg h, sg, sg_addTo k v r b]
        ring

def compact (r : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (r.foldr (fun p acc => addTo p.1 p.2 acc) []).filter (fun p => !decide (p.2 = 0))

theorem sg_foldr : ∀ (r : List (ℕ × ℤ)) (b : ℕ),
    sg (r.foldr (fun p acc => addTo p.1 p.2 acc) []) b = sg r b
  | [], b => by simp [sg]
  | (k, v) :: r, b => by
      simp [List.foldr_cons, sg_addTo, sg_foldr r b, sg]

theorem sg_filter : ∀ (l : List (ℕ × ℤ)) (b : ℕ),
    sg (l.filter (fun p => !decide (p.2 = 0))) b = sg l b
  | [], b => by simp [sg]
  | (k, w) :: l, b => by
      by_cases hw : w = 0
      · simp [List.filter_cons, hw, sg, sg_filter l b]
      · simp [List.filter_cons, hw, sg, sg_filter l b]

theorem sg_compact (r : List (ℕ × ℤ)) (b : ℕ) : sg (compact r) b = sg r b := by
  unfold compact
  rw [sg_filter, sg_foldr]

/-- Row update: leave the row alone when its pivot-column entry is zero. -/
def rowOpS (piv : List (ℕ × ℤ)) (j : ℕ) (r : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  if sg r j = 0 then r else compact (r ++ scaleNeg (sg r j * sg piv j) piv)

theorem sg_rowOpS (piv : List (ℕ × ℤ)) (j : ℕ) (r : List (ℕ × ℤ)) (b : ℕ) :
    sg (rowOpS piv j r) b = sg r b - sg r j * sg piv j * sg piv b := by
  unfold rowOpS
  by_cases h : sg r j = 0
  · simp [h]
  · rw [if_neg h, sg_compact, sg_append, sg_scaleNeg]
    ring

def tgtS : List (List (ℕ × ℤ)) → ℕ → List (ℕ × ℤ)
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, a + 1 => tgtS rs a

def cellS (tab : List (List (ℕ × ℤ))) (a b : ℕ) : ℤ := sg (tgtS tab a) b

def stepAuxS (piv : List (ℕ × ℤ)) (i j : ℕ) : ℕ → List (List (ℕ × ℤ)) → List (List (ℕ × ℤ))
  | _, [] => []
  | k, r :: rs => (if k = i then r else rowOpS piv j r) :: stepAuxS piv i j (k + 1) rs

def stepTabS (i j : ℕ) (tab : List (List (ℕ × ℤ))) : List (List (ℕ × ℤ)) :=
  stepAuxS (tgtS tab i) i j 0 tab

theorem length_stepAuxS (piv : List (ℕ × ℤ)) (i j : ℕ) :
    ∀ (rs : List (List (ℕ × ℤ))) (k : ℕ), (stepAuxS piv i j k rs).length = rs.length
  | [], k => by simp [stepAuxS]
  | r :: rs, k => by simp [stepAuxS, length_stepAuxS piv i j rs (k + 1)]

theorem length_stepTabS (i j : ℕ) (tab : List (List (ℕ × ℤ))) :
    (stepTabS i j tab).length = tab.length := length_stepAuxS _ i j tab 0

theorem tgtS_stepAuxS (piv : List (ℕ × ℤ)) (i j : ℕ) :
    ∀ (rs : List (List (ℕ × ℤ))) (k a : ℕ), a < rs.length →
      tgtS (stepAuxS piv i j k rs) a =
        if k + a = i then tgtS rs a else rowOpS piv j (tgtS rs a)
  | [], k, a, ha => by simp at ha
  | r :: rs, k, 0, _ => by simp [stepAuxS, tgtS]
  | r :: rs, k, a + 1, ha => by
      have ha' : a < rs.length := by simpa using ha
      have e : k + (a + 1) = (k + 1) + a := by omega
      rw [e]
      simp only [stepAuxS, tgtS]
      exact tgtS_stepAuxS piv i j rs (k + 1) a ha'

theorem cell_stepTabS (tab : List (List (ℕ × ℤ))) (i j a b : ℕ) (ha : a < tab.length) :
    cellS (stepTabS i j tab) a b =
      if a = i then cellS tab a b
      else cellS tab a b - cellS tab a j * cellS tab i j * cellS tab i b := by
  unfold cellS stepTabS
  rw [tgtS_stepAuxS _ _ _ tab 0 a ha]
  by_cases h : a = i
  · simp [h]
  · simp [h, sg_rowOpS]

theorem sg_zero_of_forall : ∀ (r : List (ℕ × ℤ)) (b : ℕ), (∀ p ∈ r, p.2 = 0) → sg r b = 0
  | [], b, _ => by simp [sg]
  | (k, v) :: r, b, h => by
      have hv : v = 0 := h (k, v) (by simp)
      simp [sg, hv, sg_zero_of_forall r b (fun p hp => h p (by simp [hp]))]

def allZeroExceptS (done : List ℕ) : ℕ → List (List (ℕ × ℤ)) → Bool
  | _, [] => true
  | k, r :: rs =>
      (decide (k ∈ done) || decide (∀ p ∈ r, p.2 = 0)) && allZeroExceptS done (k + 1) rs

theorem allZeroExceptS_sound (done : List ℕ) :
    ∀ (rs : List (List (ℕ × ℤ))) (k : ℕ), allZeroExceptS done k rs = true →
      ∀ a : ℕ, a < rs.length → k + a ∉ done → ∀ b : ℕ, sg (tgtS rs a) b = 0
  | [], k, _, a, ha, _, b => by simp at ha
  | r :: rs, k, h, 0, _, hnd, b => by
      simp only [allZeroExceptS, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      have hr : ∀ p ∈ r, p.2 = 0 := by
        rcases h.1 with h1 | h1
        · exact absurd (by simpa using h1) hnd
        · exact h1
      simpa [tgtS] using sg_zero_of_forall r b hr
  | r :: rs, k, h, a + 1, ha, hnd, b => by
      simp only [allZeroExceptS, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      have e : k + (a + 1) = (k + 1) + a := by omega
      have ha' : a < rs.length := by simpa using ha
      have hnd' : (k + 1) + a ∉ done := by rw [← e]; exact hnd
      simpa [tgtS] using allZeroExceptS_sound done rs (k + 1) h.2 a ha' hnd' b

def checkS (nc : ℕ) : List (List (ℕ × ℤ)) → List ℕ → List (ℕ × ℕ) → Bool
  | tab, done, [] => allZeroExceptS done 0 tab
  | tab, done, (i, j) :: t =>
      decide (i < tab.length) && decide (j < nc) && decide (i ∉ done) &&
        (decide (sg (tgtS tab i) j = 1) || decide (sg (tgtS tab i) j = -1)) &&
        checkS nc (stepTabS i j tab) (i :: done) t

theorem check_soundS (n nc : ℕ) :
    ∀ (t : List (ℕ × ℕ)) (tab : List (List (ℕ × ℤ))) (done : List ℕ), tab.length = n →
      checkS nc tab done t = true →
      ∃ t' : List (Fin n × Fin nc), t'.length = t.length ∧
        RowTrace t' (Finset.univ.filter (fun a : Fin n => a.val ∉ done))
          (fun a b => cellS tab a.val b.val)
  | [], tab, done, hn, hc => by
      simp only [checkS] at hc
      refine ⟨[], rfl, RowTrace.nil _ _ ?_⟩
      intro a ha b
      have h2 := (Finset.mem_filter.1 ha).2
      have hlt : a.val < tab.length := by have := a.isLt; omega
      have := allZeroExceptS_sound done tab 0 hc a.val hlt (by simpa using h2) b.val
      simpa [cellS] using this
  | (i, j) :: t, tab, done, hn, hc => by
      simp only [checkS, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨h1, hj⟩, hnd⟩, hu⟩, hrest⟩ := hc
      have hin : i < n := by omega
      have hlen : (stepTabS i j tab).length = n := by rw [length_stepTabS]; exact hn
      obtain ⟨t', hl, htr⟩ := check_soundS n nc t (stepTabS i j tab) (i :: done) hlen hrest
      refine ⟨(⟨i, hin⟩, ⟨j, hj⟩) :: t', by simp [hl], ?_⟩
      have hi : (⟨i, hin⟩ : Fin n) ∈ Finset.univ.filter (fun a : Fin n => a.val ∉ done) := by
        simp [Finset.mem_filter, hnd]
      have hM : pivStep (fun (a : Fin n) (b : Fin nc) => cellS tab a.val b.val)
          (⟨i, hin⟩ : Fin n) (⟨j, hj⟩ : Fin nc) =
          (fun (a : Fin n) (b : Fin nc) => cellS (stepTabS i j tab) a.val b.val) := by
        funext a b
        have hlt : a.val < tab.length := by have := a.isLt; omega
        rw [cell_stepTabS tab i j a.val b.val hlt]
        simp [pivStep, Fin.ext_iff]
      have hs : (Finset.univ.filter (fun a : Fin n => a.val ∉ done)).erase (⟨i, hin⟩ : Fin n) =
          Finset.univ.filter (fun a : Fin n => a.val ∉ (i :: done)) := by
        ext a
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
          List.mem_cons, not_or, ne_eq, Fin.ext_iff]
      refine RowTrace.cons _ _ _ _ _ hi ?_ ?_
      · simpa [cellS] using hu
      · rw [hM, hs]
        exact htr

theorem rank_of_checkS (n nc : ℕ) (tab : List (List (ℕ × ℤ))) (t : List (ℕ × ℕ))
    (hn : tab.length = n) (hc : checkS nc tab [] t = true) (K : Type) [Field K] :
    Matrix.rank (Matrix.of fun (a : Fin n) (b : Fin nc) => ((cellS tab a.val b.val : ℤ) : K))
      = t.length := by
  obtain ⟨t', hl, htr⟩ := check_soundS n nc t tab [] hn hc
  have hu : (Finset.univ.filter (fun a : Fin n => a.val ∉ ([] : List ℕ))) = Finset.univ := by
    simp
  rw [hu] at htr
  rw [← hl]
  exact rank_of_rowTrace (ι := Fin n) (κ := Fin nc) K
    (fun (a : Fin n) (b : Fin nc) => cellS tab a.val b.val) t' htr

end P2Skeleton

#print axioms P2Skeleton.rank_of_checkS
