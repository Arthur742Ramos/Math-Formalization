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

/-- A property is extensional when closed programs with identical partial
numerical behavior agree on membership. -/
def ClosedNumericallyExtensional (A : Term → Prop) : Prop :=
  ∀ t u, Scoped 0 t → Scoped 0 u →
    (∀ n, numericalValue t n = numericalValue u n) → (A t ↔ A u)

/-- Pad every output with the canonical code of its input. -/
def injectivizeSyntax {α : Type} [Primcodable α] (g : α → Term) (a : α) : Term :=
  syntaxPadding (Encodable.encode a, g a)

theorem injectivizeSyntax_computable {α : Type} [Primcodable α]
    (g : α → Term) (hg : Computable g) : Computable (injectivizeSyntax g) :=
  syntaxPadding_primrec.to_comp.comp (Computable.encode.pair hg)

theorem injectivizeSyntax_primrec {α : Type} [Primcodable α]
    (g : α → Term) (hg : Primrec g) : Primrec (injectivizeSyntax g) :=
  syntaxPadding_primrec.comp (Primrec.encode.pair hg)

theorem injectivizeSyntax_injective {α : Type} [Primcodable α]
    (g : α → Term) : Function.Injective (injectivizeSyntax g) := by
  intro a b h
  have hp := syntaxPadding_injective h
  exact Encodable.encode_injective (congrArg Prod.fst hp)

/-- Every closed-output computable transformation can be made injective
without changing membership in a closed numerical-extensional property. -/
theorem closed_extensional_injectivize {α : Type} [Primcodable α]
    (A : Term → Prop) (hA : ClosedNumericallyExtensional A)
    (g : α → Term) (hg : Computable g) (hclosed : ∀ a, Scoped 0 (g a)) :
    ∃ f : α → Term, Computable f ∧ Function.Injective f ∧
      ∀ a, Scoped 0 (f a) ∧ (A (f a) ↔ A (g a)) := by
  refine ⟨injectivizeSyntax g, injectivizeSyntax_computable g hg,
    injectivizeSyntax_injective g, ?_⟩
  intro a
  have hs : Scoped 0 (injectivizeSyntax g a) := syntaxPadding_closed _ (hclosed a)
  refine ⟨hs, hA _ _ hs (hclosed a) ?_⟩
  intro n
  exact syntaxPadding_numericalValue (Encodable.encode a) (g a) n

/-- A closed numerical-extensional language with a computable productive
complement is one-one hard for every recursively enumerable predicate. -/
theorem closed_productive_extensional_oneOne_hard {α : Type} [Primcodable α]
    (A : Term → Prop) (productive : Nat.Partrec.Code → Term) (hp : Computable productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive)
    (hA : ClosedNumericallyExtensional A) (P : α → Prop) (hP : REPred P) :
    ∃ f : α → Term, Computable f ∧ Function.Injective f ∧
      ∀ a, Scoped 0 (f a) ∧ (P a ↔ A (f a)) := by
  obtain ⟨g, hg, h⟩ := closed_productive_RE_hard A productive hp hclosed hprod P hP
  obtain ⟨f, hf, hi, hfg⟩ := closed_extensional_injectivize A hA g hg (fun a => (h a).1)
  refine ⟨f, hf, hi, ?_⟩
  intro a
  exact ⟨(hfg a).1, (h a).2.trans (hfg a).2.symm⟩

/-- If the productive map is primitive recursive, the one-one reduction is
primitive recursive as well. -/
theorem closed_productive_extensional_oneOne_primrec {α : Type} [Primcodable α]
    (A : Term → Prop) (productive : Nat.Partrec.Code → Term) (hp : Primrec productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive)
    (hA : ClosedNumericallyExtensional A) (P : α → Prop) (hP : REPred P) :
    ∃ f : α → Term, Primrec f ∧ Function.Injective f ∧
      ∀ a, Scoped 0 (f a) ∧ (P a ↔ A (f a)) := by
  obtain ⟨u, hu, h⟩ := closed_productive_uniform_primrec A productive hp hclosed hprod
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hP
  have hdom (a : α) : (Nat.Partrec.Code.eval c (Encodable.encode a)).Dom ↔ P a := by
    rw [hc]
    simp [Encodable.encodek, Part.assert]
  let g : α → Term := fun a => u (c, Encodable.encode a)
  have hg : Primrec g := hu.comp ((Primrec.const c).pair Primrec.encode)
  have hclosedg : ∀ a, Scoped 0 (g a) := fun a => (h c (Encodable.encode a)).1
  refine ⟨injectivizeSyntax g, injectivizeSyntax_primrec g hg,
    injectivizeSyntax_injective g, ?_⟩
  intro a
  have hs : Scoped 0 (injectivizeSyntax g a) := syntaxPadding_closed _ (hclosedg a)
  have he := hA _ _ hs (hclosedg a)
    (fun n => syntaxPadding_numericalValue (Encodable.encode a) (g a) n)
  exact ⟨hs, (hdom a).symm.trans ((h c (Encodable.encode a)).2.trans he.symm)⟩

/-- The concrete zero-result language satisfies the closed extensionality
hypothesis used by the general one-one theorem. -/
theorem closed_zero_extensional : ClosedNumericallyExtensional (closedNumeralAtZero 0) := by
  intro t u ht hu h
  simp only [closedNumeralAtZero, ht, hu, true_and]
  rw [← mem_numericalValue_iff, ← mem_numericalValue_iff, h 0]

/-- An r.e. closed numerical-extensional language with a computable
productive complement is one-one complete for r.e. predicates. -/
theorem closed_productive_extensional_oneOne_complete {α : Type} [Primcodable α]
    (A : Term → Prop) (productive : Nat.Partrec.Code → Term) (hp : Computable productive)
    (hclosed : ∀ t, A t → Scoped 0 t) (hprod : ClosedProductiveComplement A productive)
    (hA : ClosedNumericallyExtensional A) (hRE : REPred A) :
    REPred A ∧ ∀ P : α → Prop, REPred P → OneOneReducible P A := by
  refine ⟨hRE, ?_⟩
  intro P hP
  obtain ⟨f, hf, hi, h⟩ :=
    closed_productive_extensional_oneOne_hard A productive hp hclosed hprod hA P hP
  exact ⟨f, hf, hi, fun a => (h a).2⟩

/-- The concrete closed zero-result language satisfies every hypothesis of
the general result with a primitive-recursive productive map. -/
theorem closed_zero_extensional_creative :
    ClosedNumericallyExtensional (closedNumeralAtZero 0) ∧
      REPred (closedNumeralAtZero 0) ∧
        ∃ productive : Nat.Partrec.Code → Term, Primrec productive ∧
          ClosedProductiveComplement (closedNumeralAtZero 0) productive :=
  ⟨closed_zero_extensional, closedNumeralAtZero_re 0, closed_zero_is_productive⟩

#print axioms closed_productive_extensional_oneOne_complete
#print axioms closed_zero_extensional_creative
#print axioms closed_extensional_injectivize
#print axioms closed_productive_extensional_oneOne_hard
#print axioms closed_productive_extensional_oneOne_primrec
#print axioms closed_zero_extensional
#print axioms closed_productive_RE_hard
#print axioms closed_zero_is_productive
#print axioms closed_productive_uniform_codes
#print axioms closed_productive_uniform_primrec
#print axioms productiveSingleton_codes
end LambdaTuring
