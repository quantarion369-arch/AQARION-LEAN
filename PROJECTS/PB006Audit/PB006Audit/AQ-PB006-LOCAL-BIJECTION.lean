-- PB006Audit/AQ-PB006-LOCAL-BIJECTION.lean
-- Fixed 2026-10-06 — 3 errors from your log fixed

def mod_mod_of_dvd (a b d : Nat) (h : d ∣ b) : (a % b) % d = a % d := by
  by_cases hd0 : d = 0
  · subst hd0
    rcases h with ⟨m, hm⟩
    have hb0 : b = 0 := by simp at hm; exact hm
    rw [hb0]; simp
  · have hb : b % d = 0 := by
      rcases h with ⟨m, hm⟩
      rw [hm]
      simp [Nat.mul_mod, Nat.mod_self]
    have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have h2 : a % d = (b * (a / b) + a % b) % d := by rw [hdiv]
    have h3 : (b * (a / b)) % d = 0 := by
      calc (b * (a / b)) % d = (b % d * ((a / b) % d)) % d := by rw [Nat.mul_mod]
        _ = (0 * ((a / b) % d)) % d := by rw [hb]
        _ = 0 := by simp
    have h0 : ((a % b) % d + 0) % d = (a % b) % d := by simp
    calc (a % b) % d
        = ((a % b) % d + 0) % d := by rw [h0]
      _ = ((a % b) % d + (b * (a / b)) % d) % d := by rw [h3]
      _ = (a % b + b * (a / b)) % d := by rw [← Nat.add_mod]
      _ = (b * (a / b) + a % b) % d := by rw [Nat.add_comm]
      _ = a % d := by rw [← h2]

def Cluster {k : Nat} (c : Fin k -> Nat) := (i : Fin k) × Fin (c i)

def sigma {k : Nat} (c : Fin k -> Nat) (hc : ∀ i, 0 < c i) (p : Cluster c) : Cluster c :=
  match p with
  | ⟨i, x⟩ =>
    let y : Nat := (x.val + 1) % c i
    have hy : y < c i := Nat.mod_lt _ (hc i)
    ⟨i, ⟨y, hy⟩⟩

def phaseRel {k : Nat} (c : Fin k -> Nat) (d : Nat) (phi : Fin k -> Nat) (p q : Cluster c) : Prop :=
  (p.2.val + phi p.1) % d = (q.2.val + phi q.1) % d

theorem phaseRel_refl {k : Nat} (c : Fin k -> Nat) (d : Nat) (phi : Fin k -> Nat) (p : Cluster c) :
    phaseRel c d phi p p := by rfl
theorem phaseRel_symm {k : Nat} (c : Fin k -> Nat) (d : Nat) (phi : Fin k -> Nat) {p q : Cluster c}
    (h : phaseRel c d phi p q) : phaseRel c d phi q p := Eq.symm h
theorem phaseRel_trans {k : Nat} (c : Fin k -> Nat) (d : Nat) (phi : Fin k -> Nat) {p q r : Cluster c}
    (hpq : phaseRel c d phi p q) (hqr : phaseRel c d phi q r) : phaseRel c d phi p r := by
  unfold phaseRel at *; rw [hpq, hqr]

def phaseSetoid {k : Nat} (c : Fin k -> Nat) (d : Nat) (phi : Fin k -> Nat) : Setoid (Cluster c) where
  r := phaseRel c d phi
  iseqv := { refl := phaseRel_refl c d phi; symm := fun h => phaseRel_symm c d phi h; trans := fun h1 h2 => phaseRel_trans c d phi h1 h2 }

theorem phaseRel_invariant {k : Nat} (c : Fin k -> Nat) (hc : ∀ i, 0 < c i) (d : Nat)
    (hd : ∀ i, d ∣ c i) (phi : Fin k -> Nat) {p q : Cluster c}
    (h : phaseRel c d phi p q) : phaseRel c d phi (sigma c hc p) (sigma c hc q) := by
  unfold phaseRel at *
  rcases p with ⟨ip, xp⟩
  rcases q with ⟨iq, xq⟩
  simp only [sigma] at h ⊢
  have h1 : ((xp.val + 1) % c ip) % d = (xp.val + 1) % d := mod_mod_of_dvd _ _ _ (hd ip)
  have h2 : ((xq.val + 1) % c iq) % d = (xq.val + 1) % d := mod_mod_of_dvd _ _ _ (hd iq)
  have hl : ((xp.val + 1) % c ip + phi ip) % d = (xp.val + 1 + phi ip) % d :=
    calc ((xp.val + 1) % c ip + phi ip) % d
        = (((xp.val + 1) % c ip) % d + phi ip % d) % d := by rw [Nat.add_mod]
      _ = ((xp.val + 1) % d + phi ip % d) % d := by rw [h1]
      _ = (xp.val + 1 + phi ip) % d := by rw [← Nat.add_mod]
  have hr : ((xq.val + 1) % c iq + phi iq) % d = (xq.val + 1 + phi iq) % d :=
    calc ((xq.val + 1) % c iq + phi iq) % d
        = (((xq.val + 1) % c iq) % d + phi iq % d) % d := by rw [Nat.add_mod]
      _ = ((xq.val + 1) % d + phi iq % d) % d := by rw [h2]
      _ = (xq.val + 1 + phi iq) % d := by rw [← Nat.add_mod]
  rw [hl, hr]
  have hp : (xp.val + phi ip) % d = (xq.val + phi iq) % d := h
  calc (xp.val + 1 + phi ip) % d
      = (xp.val + (1 + phi ip)) % d := by rw [Nat.add_assoc]
    _ = (xp.val + (phi ip + 1)) % d := by rw [Nat.add_comm 1 (phi ip)]
    _ = (xp.val + phi ip + 1) % d := by rw [← Nat.add_assoc]
    _ = (((xp.val + phi ip) % d + 1 % d) % d) := by rw [Nat.add_mod]
    _ = (((xq.val + phi iq) % d + 1 % d) % d) := by rw [hp]
    _ = ((xq.val + phi iq + 1) % d) := by rw [← Nat.add_mod]
    _ = ((xq.val + (phi iq + 1)) % d) := by rw [Nat.add_assoc]
    _ = ((xq.val + (1 + phi iq)) % d) := by rw [Nat.add_comm 1 (phi iq)]
    _ = (xq.val + 1 + phi iq) % d := by rw [← Nat.add_assoc]

#check Cluster
#check sigma
#check phaseRel
#check mod_mod_of_dvd
#check phaseRel_invariant
