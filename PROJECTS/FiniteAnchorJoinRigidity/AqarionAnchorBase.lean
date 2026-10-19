import Lean.Elab.Tactic.Omega

universe u

namespace AqarionStructuralRigidity

variable {X : Type u}

theorem pullback_rigidity_of_quotient_selfmap_principle
    (T : X → X) (E : Setoid X)
    (hfinite :
      ∀ f : Quotient E → Quotient E,
        (∀ a b, f a = f b → a = b) →
        ∀ b, ∃ a, f a = b)
    (hback :
      ∀ x y, E.r (T x) (T y) → E.r x y) :
    ∀ x y, E.r x y ↔ E.r (T x) (T y) := by
  let q : X → Quotient E := Quotient.mk E

  have hex (a : Quotient E) : ∃ x : X, q x = a := by
    refine Quotient.inductionOn a ?_
    intro x
    exact ⟨x, rfl⟩

  let rep : Quotient E → X :=
    fun a => Classical.choose (hex a)

  have hrep (a : Quotient E) : q (rep a) = a := by
    exact Classical.choose_spec (hex a)

  let f : Quotient E → Quotient E :=
    fun a => q (T (rep a))

  have hinj : ∀ a b, f a = f b → a = b := by
    intro a b hab
    have hrel : E.r (T (rep a)) (T (rep b)) :=
      Quotient.exact hab
    have heq : q (rep a) = q (rep b) :=
      Quotient.sound (hback (rep a) (rep b) hrel)
    exact (hrep a).symm.trans (heq.trans (hrep b))

  have hsurj : ∀ b, ∃ a, f a = b :=
    hfinite f hinj

  have hcanonical (x : X) : f (q x) = q (T x) := by
    obtain ⟨a, ha⟩ := hsurj (q (T x))
    have hrel : E.r (T (rep a)) (T x) :=
      Quotient.exact ha
    have heq : q (rep a) = q x :=
      Quotient.sound (hback (rep a) x hrel)
    have hclass : a = q x :=
      (hrep a).symm.trans heq
    exact (congrArg f hclass).symm.trans ha

  intro x y
  constructor
  · intro hxy
    have hclasses : q x = q y :=
      Quotient.sound hxy
    have himages : q (T x) = q (T y) :=
      (hcanonical x).symm.trans
        ((congrArg f hclasses).trans (hcanonical y))
    exact Quotient.exact himages
  · exact hback x y

#print axioms pullback_rigidity_of_quotient_selfmap_principle
#print pullback_rigidity_of_quotient_selfmap_principle

end AqarionStructuralRigidity


namespace AqarionFiniteBridge


def compress {n : Nat} (p x : Fin (n + 1))
    (hx : x ≠ p) : Fin n :=
  ⟨if x.val < p.val then x.val else x.val - 1, by
    have hxn := x.isLt
    have hpn := p.isLt
    have hne : x.val ≠ p.val := by
      intro h
      exact hx (Fin.ext h)
    split <;> omega⟩

theorem compress_injective {n : Nat}
    (p x y : Fin (n + 1))
    (hx : x ≠ p) (hy : y ≠ p)
    (h : compress p x hx = compress p y hy) :
    x = y := by
  have hv := congrArg Fin.val h
  have hxn := x.isLt
  have hyn := y.isLt
  have hpn := p.isLt
  have hnx : x.val ≠ p.val := by
    intro he
    exact hx (Fin.ext he)
  have hny : y.val ≠ p.val := by
    intro he
    exact hy (Fin.ext he)
  apply Fin.ext
  by_cases hxp : x.val < p.val
  · by_cases hyp : y.val < p.val
    · simp [compress, hxp, hyp] at hv
      omega
    · simp [compress, hxp, hyp] at hv
      omega
  · by_cases hyp : y.val < p.val
    · simp [compress, hxp, hyp] at hv
      omega
    · simp [compress, hxp, hyp] at hv
      omega

theorem no_injection_successor (n : Nat) :
    ∀ f : Fin (n + 1) → Fin n,
      (∀ a b, f a = f b → a = b) → False := by
  induction n with
  | zero =>
      intro f hinj
      have h := (f ⟨0, by omega⟩).isLt
      omega
  | succ n ih =>
      intro f hinj
      let last : Fin (n + 1 + 1) := ⟨n + 1, by omega⟩
      let emb : Fin (n + 1) → Fin (n + 1 + 1) :=
        fun i => ⟨i.val, by have h := i.isLt; omega⟩
      let pivot : Fin (n + 1) := f last

      have havoid (i : Fin (n + 1)) :
          f (emb i) ≠ pivot := by
        intro he
        have hh := congrArg Fin.val (hinj (emb i) last he)
        have hi := i.isLt
        dsimp [emb, last] at hh
        omega

      let g : Fin (n + 1) → Fin n :=
        fun i => compress pivot (f (emb i)) (havoid i)

      have hg : ∀ a b, g a = g b → a = b := by
        intro a b hab
        have hcomp :
            compress pivot (f (emb a)) (havoid a) =
            compress pivot (f (emb b)) (havoid b) := hab
        have hf :
            f (emb a) = f (emb b) :=
          compress_injective pivot
            (f (emb a)) (f (emb b))
            (havoid a) (havoid b) hcomp
        have hemb := hinj (emb a) (emb b) hf
        apply Fin.ext
        exact congrArg (fun z : Fin (n + 1 + 1) => z.val) hemb

      exact ih g hg

theorem fin_injective_implies_surjective (n : Nat) :
    ∀ f : Fin n → Fin n,
      (∀ a b, f a = f b → a = b) →
      ∀ b, ∃ a, f a = b := by
  cases n with
  | zero =>
      intro f hinj b
      exact Fin.elim0 b
  | succ n =>
      intro f hinj b
      classical
      by_cases hb : ∃ a, f a = b
      · exact hb
      · have havoid (a : Fin (n + 1)) : f a ≠ b := by
          intro h
          exact hb ⟨a, h⟩

        let g : Fin (n + 1) → Fin n :=
          fun a => compress b (f a) (havoid a)

        have hg : ∀ a c, g a = g c → a = c := by
          intro a c hac
          have hcomp :
              compress b (f a) (havoid a) =
              compress b (f c) (havoid c) := hac
          have hf : f a = f c :=
            compress_injective b (f a) (f c)
              (havoid a) (havoid c) hcomp
          exact hinj a c hf

        exact False.elim (no_injection_successor n g hg)

theorem selfmap_principle_of_encoding
    {Q : Type u} (n : Nat)
    (enc : Q → Fin n) (dec : Fin n → Q)
    (hleft : ∀ a, dec (enc a) = a)
    (hright : ∀ i, enc (dec i) = i)
    (f : Q → Q)
    (hinj : ∀ a b, f a = f b → a = b) :
    ∀ b, ∃ a, f a = b := by
  let g : Fin n → Fin n := fun i => enc (f (dec i))

  have hg : ∀ a b, g a = g b → a = b := by
    intro a b hab
    have hf : f (dec a) = f (dec b) := by
      have hh := congrArg dec hab
      simpa only [g, hleft] using hh
    have hd : dec a = dec b := hinj (dec a) (dec b) hf
    have hh := congrArg enc hd
    simpa only [hright] using hh

  intro b
  obtain ⟨i, hi⟩ :=
    fin_injective_implies_surjective n g hg (enc b)
  refine ⟨dec i, ?_⟩
  have hh := congrArg dec hi
  simpa only [g, hleft] using hh

theorem finite_quotient_pullback_rigidity
    {X : Type u} (T : X → X) (E : Setoid X)
    (n : Nat)
    (enc : Quotient E → Fin n)
    (dec : Fin n → Quotient E)
    (hleft : ∀ a, dec (enc a) = a)
    (hright : ∀ i, enc (dec i) = i)
    (hback : ∀ x y, E.r (T x) (T y) → E.r x y) :
    ∀ x y, E.r x y ↔ E.r (T x) (T y) := by
  apply AqarionStructuralRigidity.pullback_rigidity_of_quotient_selfmap_principle T E
  · intro f hinj
    exact selfmap_principle_of_encoding
      n enc dec hleft hright f hinj
  · exact hback

#print axioms fin_injective_implies_surjective
#print axioms finite_quotient_pullback_rigidity
#print finite_quotient_pullback_rigidity

end AqarionFiniteBridge

namespace AqarionAnchor

def orbit {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | k + 1, x => f (orbit f k x)

theorem orbit_cancel {A : Type}
    (f : A → A)
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ i d x, orbit f i x = orbit f (i + d) x →
      x = orbit f d x := by
  intro i
  induction i with
  | zero =>
      intro d x h
      simpa only [Nat.zero_add, orbit] using h
  | succ i ih =>
      intro d x h
      have hi : i + 1 + d = (i + d) + 1 := by omega
      rw [hi] at h
      change f (orbit f i x) = f (orbit f (i + d) x) at h
      exact ih d x (hf _ _ h)

theorem selfmap_principle_of_injection {A : Type}
    (n : Nat) (encode : A → Fin n)
    (hencode : ∀ a b, encode a = encode b → a = b)
    (f : A → A)
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ b, ∃ a, f a = b := by
  classical
  intro b
  by_cases hb : ∃ a, f a = b
  · exact hb
  · have hmissing : ∀ a, f a ≠ b := by
      intro a ha
      exact hb ⟨a, ha⟩

    have hdistinct :
        ∀ i j, i < j → orbit f i b ≠ orbit f j b := by
      intro i j hij heq
      let d := j - i - 1
      have hj : j = i + (d + 1) := by
        dsimp [d]
        omega
      rw [hj] at heq
      have hcycle : b = orbit f (d + 1) b :=
        orbit_cancel f hf i (d + 1) b heq
      exact hmissing (orbit f d b) hcycle.symm

    let g : Fin (n + 1) → Fin n :=
      fun i => encode (orbit f i.val b)

    have hg : ∀ a c, g a = g c → a = c := by
      intro a c hac
      have heq : orbit f a.val b = orbit f c.val b :=
        hencode _ _ hac
      apply Fin.ext
      by_cases hlt : a.val < c.val
      · exact False.elim (hdistinct _ _ hlt heq)
      · by_cases hgt : c.val < a.val
        · exact False.elim (hdistinct _ _ hgt heq.symm)
        · omega

    exact False.elim
      (AqarionFiniteBridge.no_injection_successor n g hg)

theorem injective_of_surjective {A : Type}
    (hfinite :
      ∀ f : A → A,
        (∀ a b, f a = f b → a = b) →
        ∀ b, ∃ a, f a = b)
    (f : A → A)
    (hsurj : ∀ b, ∃ a, f a = b) :
    ∀ a b, f a = f b → a = b := by
  let s : A → A := fun b => Classical.choose (hsurj b)
  have hs (b : A) : f (s b) = b :=
    Classical.choose_spec (hsurj b)

  have hsinj : ∀ a b, s a = s b → a = b := by
    intro a b hab
    exact (hs a).symm.trans ((congrArg f hab).trans (hs b))

  have hssurj := hfinite s hsinj

  have hleft (a : A) : s (f a) = a := by
    obtain ⟨b, hb⟩ := hssurj a
    have hfa : f a = b :=
      (congrArg f hb).symm.trans (hs b)
    exact (congrArg s hfa).trans hb

  intro a b hab
  exact (hleft a).symm.trans
    ((congrArg s hab).trans (hleft b))

theorem finite_anchor_rigidity
    {X : Type} (T : X → X) (E J : Setoid X)
    (n : Nat)
    (enc : Quotient E → Fin n)
    (dec : Fin n → Quotient E)
    (hleft : ∀ a, dec (enc a) = a)
    (hright : ∀ i, enc (dec i) = i)
    (hback : ∀ x y, E.r (T x) (T y) → E.r x y)
    (hle : ∀ x y, E.r x y → J.r x y)
    (hforward : ∀ x y, J.r x y → J.r (T x) (T y)) :
    ∀ x y, J.r x y ↔ J.r (T x) (T y) := by
  let qE : X → Quotient E := Quotient.mk E
  let qJ : X → Quotient J := Quotient.mk J

  have hexE (a : Quotient E) : ∃ x : X, qE x = a := by
    refine Quotient.inductionOn a ?_
    intro x
    exact ⟨x, rfl⟩
  let repE : Quotient E → X :=
    fun a => Classical.choose (hexE a)
  have hrepE (a : Quotient E) : qE (repE a) = a :=
    Classical.choose_spec (hexE a)

  have hexJ (a : Quotient J) : ∃ x : X, qJ x = a := by
    refine Quotient.inductionOn a ?_
    intro x
    exact ⟨x, rfl⟩
  let repJ : Quotient J → X :=
    fun a => Classical.choose (hexJ a)
  have hrepJ (a : Quotient J) : qJ (repJ a) = a :=
    Classical.choose_spec (hexJ a)

  let encodeJ : Quotient J → Fin n :=
    fun a => enc (qE (repJ a))

  have hencodeJ :
      ∀ a b, encodeJ a = encodeJ b → a = b := by
    intro a b hab
    have heq : qE (repJ a) = qE (repJ b) := by
      have hh := congrArg dec hab
      simpa only [encodeJ, hleft] using hh
    have hrel : E.r (repJ a) (repJ b) :=
      Quotient.exact heq
    have hj : qJ (repJ a) = qJ (repJ b) :=
      Quotient.sound (hle _ _ hrel)
    exact (hrepJ a).symm.trans (hj.trans (hrepJ b))

  let fE : Quotient E → Quotient E :=
    fun a => qE (T (repE a))

  have hfE : ∀ a b, fE a = fE b → a = b := by
    intro a b hab
    have hrel : E.r (T (repE a)) (T (repE b)) :=
      Quotient.exact hab
    have heq : qE (repE a) = qE (repE b) :=
      Quotient.sound (hback _ _ hrel)
    exact (hrepE a).symm.trans (heq.trans (hrepE b))

  have hsurjE : ∀ b, ∃ a, fE a = b :=
    AqarionFiniteBridge.selfmap_principle_of_encoding
      n enc dec hleft hright fE hfE

  let fJ : Quotient J → Quotient J :=
    Quotient.lift
      (fun x => qJ (T x))
      (fun x y h => Quotient.sound (hforward x y h))

  have hsurjJ : ∀ b, ∃ a, fJ a = b := by
    intro b
    obtain ⟨a, ha⟩ := hsurjE (qE (repJ b))
    have he : E.r (T (repE a)) (repJ b) :=
      Quotient.exact ha
    have hj : qJ (T (repE a)) = qJ (repJ b) :=
      Quotient.sound (hle _ _ he)
    refine ⟨qJ (repE a), ?_⟩
    change qJ (T (repE a)) = b
    exact hj.trans (hrepJ b)

  have hinjJ : ∀ a b, fJ a = fJ b → a = b :=
    injective_of_surjective
      (selfmap_principle_of_injection n encodeJ hencodeJ)
      fJ hsurjJ

  intro x y
  constructor
  · exact hforward x y
  · intro h
    have himages : fJ (qJ x) = fJ (qJ y) :=
      Quotient.sound h
    exact Quotient.exact (hinjJ _ _ himages)

#print axioms selfmap_principle_of_injection
#print axioms injective_of_surjective
#print axioms finite_anchor_rigidity
#print finite_anchor_rigidity

end AqarionAnchor
