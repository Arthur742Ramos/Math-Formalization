/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.CreativeZero
public meta import LambdaTuring.CreativeZero

@[expose] public section

namespace LambdaTuring

/-- A uniform recognizer which, on a coded parameter `(e,n)`, accepts only
the productive map applied to its own specialized code, and only if `e n`
is defined. Invalid parameter encodings have a fixed fallback. -/
def productiveSingletonSimulation (productive : Nat.Partrec.Code → Term)
    (p : Nat.Partrec.Code × Nat) : Part Nat :=
  let a := (Nat.unpair p.2).1
  let x := (Nat.unpair p.2).2
  let en := (Encodable.decode a : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)
  let self := Nat.Partrec.Code.curry p.1 a
  if x = executableTermEncode (productive self) then Nat.Partrec.Code.eval en.1 en.2 else Part.none

theorem productiveSingletonSimulation_partrec (productive : Nat.Partrec.Code → Term)
    (hp : Computable productive) : Partrec (productiveSingletonSimulation productive) := by
  let P := Nat.Partrec.Code × Nat
  have ha : Primrec (fun p : P => (Nat.unpair p.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hx : Primrec (fun p : P => (Nat.unpair p.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hen : Primrec (fun p : P =>
      (Encodable.decode ((Nat.unpair p.2).1) : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp ha
  have hself : Primrec (fun p : P => Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1) :=
    Nat.Partrec.Code.primrec₂_curry.comp Primrec.fst ha
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have htarget : Computable (fun p : P =>
      executableTermEncode (productive (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1))) :=
    henc.comp (hp.comp hself.to_comp)
  have heq : Computable (fun p : Nat × Nat => decide (p.1 = p.2)) :=
    (Primrec.eq.comp Primrec.fst Primrec.snd).decide.to_comp
  have htest : Computable (fun p : P =>
      decide ((Nat.unpair p.2).2 =
        executableTermEncode (productive (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1)))) :=
    heq.comp (hx.to_comp.pair htarget)
  have heval : Partrec (fun p : P => Nat.Partrec.Code.eval
      ((Encodable.decode ((Nat.unpair p.2).1) : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)).1
      ((Encodable.decode ((Nat.unpair p.2).1) : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)).2) :=
    Nat.Partrec.Code.eval_part.comp (Computable.fst.comp hen.to_comp) (Computable.snd.comp hen.to_comp)
  apply (Partrec.cond htest heval Partrec.none).of_eq
  intro p
  simp only [productiveSingletonSimulation, Bool.cond_eq_ite, decide_eq_true_eq]

/-- Every computable productive map induces a primitive-recursive family of
recognizer codes whose domains are the indicated singleton or empty set. -/
theorem productiveSingleton_codes (productive : Nat.Partrec.Code → Term)
    (hp : Computable productive) :
    ∃ q : Nat.Partrec.Code × Nat → Nat.Partrec.Code, Primrec q ∧
      ∀ e n t, codeAcceptsTerm (q (e, n)) t ↔
        t = productive (q (e, n)) ∧ (Nat.Partrec.Code.eval e n).Dom := by
  have hsim : Partrec₂ (fun u z => productiveSingletonSimulation productive (u, z)) :=
    (productiveSingletonSimulation_partrec productive hp).to₂
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.fixed_point₂ hsim
  let q : Nat.Partrec.Code × Nat → Nat.Partrec.Code :=
    fun p => Nat.Partrec.Code.curry u (Encodable.encode p)
  have hq : Primrec q := Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode
  refine ⟨q, hq, ?_⟩
  intro e n t
  have heval : Nat.Partrec.Code.eval (q (e, n)) (executableTermEncode t) =
      if executableTermEncode t = executableTermEncode (productive (q (e, n))) then
        Nat.Partrec.Code.eval e n else Part.none := by
    change Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (Encodable.encode (e, n)))
      (executableTermEncode t) = _
    rw [Nat.Partrec.Code.eval_curry, hu]
    simp only [productiveSingletonSimulation, Nat.unpair_pair, Encodable.encodek,
      Option.getD_some, q]
  have henc : executableTermEncode t = executableTermEncode (productive (q (e, n))) ↔
      t = productive (q (e, n)) := by
    constructor
    · intro h
      apply Encodable.encode_injective
      simpa only [executableTermEncode_eq] using h
    · rintro rfl
      rfl
  unfold codeAcceptsTerm
  rw [heval]
  by_cases h : t = productive (q (e, n))
  · subst t
    simp
  · have hne : executableTermEncode t ≠ executableTermEncode (productive (q (e, n))) :=
      fun h' => h (henc.mp h')
    simp [h, hne]

/-- A productive-complement witness is required to defeat every recursive
recognizer that avoids `A` on closed syntax. -/
def ClosedProductiveComplement (A : Term → Prop) (productive : Nat.Partrec.Code → Term) : Prop :=
  ∀ c, (∀ t, Scoped 0 t → codeAcceptsTerm c t → ¬ A t) →
    Scoped 0 (productive c) ∧ ¬ A (productive c) ∧ ¬ codeAcceptsTerm c (productive c)

/-- A computable productive complement of a closed-term language gives a
uniform reduction of recursive-code halting. The recognizer-code map itself
is primitive recursive, after choosing one fixed point by existence. -/
theorem closed_productive_uniform_codes (A : Term → Prop)
    (productive : Nat.Partrec.Code → Term) (hp : Computable productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive) :
    ∃ q : Nat.Partrec.Code × Nat → Nat.Partrec.Code, Primrec q ∧
      ∀ e n, Scoped 0 (productive (q (e, n))) ∧
        ((Nat.Partrec.Code.eval e n).Dom ↔ A (productive (q (e, n)))) := by
  obtain ⟨q, hq, hsingle⟩ := productiveSingleton_codes productive hp
  refine ⟨q, hq, ?_⟩
  intro e n
  by_cases hd : (Nat.Partrec.Code.eval e n).Dom
  · have hA : A (productive (q (e, n))) := by
      by_contra hn
      have hsubset : ∀ t, Scoped 0 t → codeAcceptsTerm (q (e, n)) t → ¬ A t := by
        intro t _ ht
        have heq := ((hsingle e n t).1 ht).1
        simpa only [heq] using hn
      have hout := hprod (q (e, n)) hsubset
      exact hout.2.2 ((hsingle e n _).2 ⟨rfl, hd⟩)
    exact ⟨hclosed _ hA, by simp [hd, hA]⟩
  · have hsubset : ∀ t, Scoped 0 t → codeAcceptsTerm (q (e, n)) t → ¬ A t := by
      intro t _ ht
      exact False.elim (hd ((hsingle e n t).1 ht).2)
    obtain ⟨hs, hn, _⟩ := hprod (q (e, n)) hsubset
    exact ⟨hs, by simp [hd, hn]⟩

/-- A primitive-recursive productive map yields a primitive-recursive
many-one reduction of universal code halting to the closed language. -/
theorem closed_productive_uniform_primrec (A : Term → Prop)
    (productive : Nat.Partrec.Code → Term) (hp : Primrec productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive) :
    ∃ f : Nat.Partrec.Code × Nat → Term, Primrec f ∧
      ∀ e n, Scoped 0 (f (e, n)) ∧ ((Nat.Partrec.Code.eval e n).Dom ↔ A (f (e, n))) := by
  obtain ⟨q, hq, h⟩ := closed_productive_uniform_codes A productive hp.to_comp hclosed hprod
  exact ⟨fun p => productive (q p), hp.comp hq, h⟩

/-- Every r.e. predicate on a primcodable domain computably reduces to a
closed language with a computable productive complement. -/
theorem closed_productive_RE_hard {α : Type} [Primcodable α]
    (A : Term → Prop) (productive : Nat.Partrec.Code → Term) (hp : Computable productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive)
    (P : α → Prop) (hP : REPred P) :
    ∃ f : α → Term, Computable f ∧ ∀ a, Scoped 0 (f a) ∧ (P a ↔ A (f a)) := by
  obtain ⟨q, hq, h⟩ := closed_productive_uniform_codes A productive hp hclosed hprod
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hP
  have hdom (a : α) : (Nat.Partrec.Code.eval c (Encodable.encode a)).Dom ↔ P a := by
    rw [hc]
    simp [Encodable.encodek, Part.assert]
  let f : α → Term := fun a => productive (q (c, Encodable.encode a))
  have hf : Computable f := hp.comp (hq.to_comp.comp ((Computable.const c).pair Computable.encode))
  refine ⟨f, hf, ?_⟩
  intro a
  exact ⟨(h c (Encodable.encode a)).1,
    (hdom a).symm.trans (h c (Encodable.encode a)).2⟩

/-- The concrete closed zero-result language supplies the productive map,
so the general construction applies to the developed lambda language. -/
theorem closed_zero_is_productive :
    ∃ productive : Nat.Partrec.Code → Term,
      Primrec productive ∧ ClosedProductiveComplement (closedNumeralAtZero 0) productive := by
  obtain ⟨productive, hp, hprod⟩ := closed_zero_productive_complement
  exact ⟨productive, hp, hprod⟩

#print axioms closed_productive_RE_hard
#print axioms closed_zero_is_productive
#print axioms closed_productive_uniform_codes
#print axioms closed_productive_uniform_primrec
#print axioms productiveSingleton_codes
end LambdaTuring
