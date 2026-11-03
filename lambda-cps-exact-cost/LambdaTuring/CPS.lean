/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ConstantCompiler
public meta import LambdaTuring.ConstantCompiler
public import LambdaTuring.SearchComputable
public meta import LambdaTuring.SearchComputable

@[expose] public section

/- The strict CPS invariant and normalisation argument follow the related
   Isabelle development's Lambda_CPS theory and the continuation method
   credited there to Norrish (2011). -/

namespace LambdaTuring

theorem scoped_mono {t : Term} {k l : Nat} (h : Scoped k t) (hle : k ≤ l) : Scoped l t := by
  induction t generalizing k l with
  | var i => exact Nat.lt_of_lt_of_le h hle
  | abs t ih => exact ih h (Nat.add_le_add_right hle 1)
  | app f x ihf ihx => exact ⟨ihf h.1 hle, ihx h.2 hle⟩

theorem liftFrom_scoped (t : Term) (depth cutoff : Nat)
    (h : Scoped depth t) (hle : depth ≤ cutoff) : liftFrom cutoff t = t := by
  induction t generalizing depth cutoff with
  | var i =>
    have hi : i < cutoff := Nat.lt_of_lt_of_le h hle
    simp [liftFrom, hi]
  | abs body ih =>
    change Term.abs (liftFrom (cutoff + 1) body) = Term.abs body
    rw [ih (depth + 1) (cutoff + 1) h (Nat.add_le_add_right hle 1)]
  | app f x ihf ihx =>
    change Term.app (liftFrom cutoff f) (liftFrom cutoff x) = Term.app f x
    rw [ihf depth cutoff h.1 hle, ihx depth cutoff h.2 hle]

/-- Substitution outside the scope of all variables leaves a term unchanged. -/
theorem substAt_scoped (t : Term) (depth : Nat) (value : Term)
    (h : Scoped depth t) : substAt depth value t = t := by
  induction t generalizing depth with
  | var i =>
    have hi : i < depth := h
    simp [substAt, Nat.ne_of_lt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
  | abs body ih =>
    change Term.abs (substAt (depth + 1) value body) = Term.abs body
    rw [ih (depth + 1) h]
  | app f x ihf ihx =>
    change Term.app (substAt depth value f) (substAt depth value x) = Term.app f x
    rw [ihf depth h.1, ihx depth h.2]

theorem reaches_appLeft {a b : Term} (h : Reaches a b) (x : Term) :
    Reaches (.app a x) (.app b x) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appLeft s) ih

theorem reaches_appRight (f : Term) {a b : Term} (h : Reaches a b) :
    Reaches (.app f a) (.app f b) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appRight s) ih

/-- A numeral reachable before and after another reduction is reachable from
    the intermediate term, by confluence and normality of Church numerals. -/
theorem reaches_numeral_join {a b : Term} {m : Nat}
    (hab : Reaches a b) (ham : Reaches a (church m)) : Reaches b (church m) := by
  obtain ⟨u, hbu, hmu⟩ := beta_confluent hab ham
  have heq : church m = u := normal_reaches_eq (church_no_beta m) hmu
  simpa [← heq] using hbu

/-- A CPS program invokes its continuation on every defined result; when the
    computation is undefined, no supplied continuation yields a normal form.
    This stronger invariant enforces strictness under full beta reduction. -/
def CPSRepresents (C : Term) (f : Nat →. Nat) : Prop :=
  Scoped 0 C ∧ ∀ n K,
    (∀ m, m ∈ f n → Reaches (.app (.app C (church n)) K) (.app K (church m))) ∧
    (f n = Part.none → ¬ ∃ N, Reaches (.app (.app C (church n)) K) N ∧ ¬ ∃ u, Beta N u)

def cpsUnary (C : Term) : Term := .abs (.app (.app C (.var 0)) identityTerm)

theorem cpsUnary_closed {C : Term} (hc : Scoped 0 C) : Scoped 0 (cpsUnary C) := by
  change Scoped 1 (.app (.app C (.var 0)) identityTerm)
  simp only [Scoped, identityTerm]
  exact ⟨⟨scoped_mono hc (Nat.zero_le 1), by decide⟩, by decide⟩

theorem cpsUnary_beta {C : Term} (hc : Scoped 0 C) (n : Nat) :
    Reaches (.app (cpsUnary C) (church n)) (.app (.app C (church n)) identityTerm) := by
  apply Reaches.step (Beta.contract _ _)
  have hC := substAt_scoped C 0 (church n) hc
  simp [substAt, identityTerm, hC]
  exact Reaches.refl _

theorem cpsUnary_produces {C : Term} {f : Nat →. Nat} (hc : CPSRepresents C f)
    {n m : Nat} (hm : m ∈ f n) : NumericalResult (cpsUnary C) n m := by
  apply reaches_trans (cpsUnary_beta hc.1 n)
  apply reaches_trans ((hc.2 n identityTerm).1 m hm)
  exact Reaches.step (Beta.contract _ _) (Reaches.refl _)

/-- The strict CPS invariant implies exact numerical representation. -/
theorem cpsUnary_represents {C : Term} {f : Nat →. Nat} (hc : CPSRepresents C f) :
    Represents (cpsUnary C) f := by
  constructor
  · exact cpsUnary_closed hc.1
  · intro n
    apply Part.ext
    intro m
    rw [mem_numericalValue_iff]
    constructor
    · intro hr
      by_cases hd : (f n).Dom
      · obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 hd
        have hresult := cpsUnary_produces hc hk
        have heq : m = k := numeral_result_unique hr hresult
        simpa [heq] using hk
      · have hnone : f n = Part.none := by
          apply Part.eq_none_iff.2
          intro x hx
          exact hd (Part.dom_iff_mem.2 ⟨x, hx⟩)
        have hjoin := reaches_numeral_join (cpsUnary_beta hc.1 n) hr
        exact False.elim ((hc.2 n identityTerm).2 hnone ⟨church m, hjoin, church_no_beta m⟩)
    · exact cpsUnary_produces hc

/-- CPS program for a constant function. -/
def cpsConstant (n : Nat) : Term := .abs (.abs (.app (.var 0) (church n)))

theorem cpsConstant_run (n input : Nat) (K : Term) :
    Reaches (.app (.app (cpsConstant n) (church input)) K) (.app K (church n)) := by
  have hs1 : Scoped 1 (church n) := scoped_mono (church_closed n) (Nat.zero_le 1)
  have h1 := substAt_scoped (church n) 1 (church input) hs1
  have h0 := substAt_scoped (church n) 0 K (church_closed n)
  have hb1 : Beta (.app (cpsConstant n) (church input)) (.abs (.app (.var 0) (church n))) := by
    simpa [cpsConstant, substAt, h1] using
      (Beta.contract (.abs (.app (.var 0) (church n))) (church input))
  have hb2 : Beta (.app (.abs (.app (.var 0) (church n))) K) (.app K (church n)) := by
    simpa [substAt, liftBy, h0] using (Beta.contract (.app (.var 0) (church n)) K)
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

theorem cpsConstant_represents (n : Nat) : CPSRepresents (cpsConstant n) (Nat.Partrec.Code.eval (Nat.Partrec.Code.const n)) := by
  constructor
  · change Scoped 2 (.app (.var 0) (church n))
    exact ⟨by simp [Scoped], scoped_mono (church_closed n) (Nat.zero_le 2)⟩
  · intro input K
    constructor
    · intro m hm
      have heq : m = n := by simpa using hm
      subst m
      exact cpsConstant_run n input K
    · intro hnone
      simp at hnone

/-- CPS identity: pass the input numeral to the continuation. -/
def cpsIdentity : Term := .abs (.abs (.app (.var 0) (.var 1)))

theorem cpsIdentity_run (input : Nat) (K : Term) :
    Reaches (.app (.app cpsIdentity (church input)) K) (.app K (church input)) := by
  have hlift : liftFrom 0 (church input) = church input :=
    liftFrom_scoped (church input) 0 0 (church_closed input) (le_refl _)
  have h0 := substAt_scoped (church input) 0 K (church_closed input)
  have hb1 : Beta (.app cpsIdentity (church input)) (.abs (.app (.var 0) (church input))) := by
    simpa [cpsIdentity, substAt, liftBy, hlift] using
      (Beta.contract (.abs (.app (.var 0) (.var 1))) (church input))
  have hb2 : Beta (.app (.abs (.app (.var 0) (church input))) K) (.app K (church input)) := by
    simpa [substAt, liftBy, h0] using (Beta.contract (.app (.var 0) (church input)) K)
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

theorem cpsIdentity_represents : CPSRepresents cpsIdentity (Nat.Partrec.Code.eval Nat.Partrec.Code.id) := by
  constructor
  · simp [cpsIdentity, Scoped]
  · intro input K
    constructor
    · intro m hm
      have heq : m = input := by simpa using hm
      subst m
      exact cpsIdentity_run input K
    · intro hnone
      simp at hnone

/-- Explicit CPS compiler for canonical constants and identity. Unsupported
    codes return `none`; this is a syntactic result, not semantic divergence. -/
def compileCPSBase (c : Nat.Partrec.Code) : Option Term :=
  if Encodable.encode c = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
  else (decodeConst c).map cpsConstant

theorem compileCPSBase_id : compileCPSBase Nat.Partrec.Code.id = some cpsIdentity := by
  simp [compileCPSBase]

theorem compileCPSBase_const (n : Nat) :
    compileCPSBase (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  have hne : Nat.Partrec.Code.const n ≠ Nat.Partrec.Code.id := by
    cases n <;> simp [Nat.Partrec.Code.const, Nat.Partrec.Code.id]
  have h : Encodable.encode (Nat.Partrec.Code.const n) ≠ Encodable.encode Nat.Partrec.Code.id :=
    fun eq => hne (Encodable.encode_injective eq)
  simp [compileCPSBase, h, decodeConst_const]

theorem compileCPSBase_sound (c : Nat.Partrec.Code) (t : Term) (h : compileCPSBase c = some t) :
    CPSRepresents t (Nat.Partrec.Code.eval c) := by
  by_cases hc : Encodable.encode c = Encodable.encode Nat.Partrec.Code.id
  · have heq : c = Nat.Partrec.Code.id := Encodable.encode_injective hc
    subst c
    have ht : cpsIdentity = t := by simpa [compileCPSBase] using h
    subst t
    exact cpsIdentity_represents
  · have hm : (decodeConst c).map cpsConstant = some t := by simpa [compileCPSBase, hc] using h
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hm
    have heq := decodeConst_sound c n hn
    subst c
    exact cpsConstant_represents n

theorem primrec_cpsConstant : Primrec cpsConstant :=
  primrec_abs.comp (primrec_abs.comp (primrec_app.comp (Primrec.const (Term.var 0)) primrec_church))

theorem primrec_compileCPSBase : Primrec compileCPSBase :=
  Primrec.ite (Primrec.eq.comp Primrec.encode (Primrec.const (Encodable.encode Nat.Partrec.Code.id)))
    (Primrec.const (some cpsIdentity)) ((Primrec.option_map₁ primrec_cpsConstant).comp primrec_decodeConst)

#print axioms substAt_scoped
#print axioms reaches_numeral_join
#print axioms cpsUnary_represents
#print axioms cpsConstant_represents
#print axioms cpsIdentity_represents
#print axioms compileCPSBase_sound
#print axioms primrec_compileCPSBase

end LambdaTuring
