/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.LambdaTotality
@[expose] public section
namespace LambdaTuring

def boundedTotalityWitness (p : (Nat.Partrec.Code × Nat) × Nat) : Bool :=
  (Nat.Partrec.Code.evaln p.2 p.1.1 p.1.2).isSome

theorem boundedTotalityWitness_primrec : Primrec boundedTotalityWitness := by
  have hr : Primrec (fun p : (Nat.Partrec.Code × Nat) × Nat => ((p.2, p.1.1), p.1.2)) :=
    (Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp hr)

theorem eval_dom_iff_bounded (c : Nat.Partrec.Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔ ∃ k, boundedTotalityWitness ((c, n), k) = true := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨k, ?_⟩
    cases he : Nat.Partrec.Code.evaln k c n with
    | none => simp [he] at hk
    | some v => simp [boundedTotalityWitness, he]
  · rintro ⟨k, hk⟩
    cases he : Nat.Partrec.Code.evaln k c n with
    | none => simp [boundedTotalityWitness, he] at hk
    | some v =>
      refine ⟨v, Nat.Partrec.Code.evaln_complete.mpr ⟨k, ?_⟩⟩
      simp [he]

theorem codeTotal_iff_bounded (c : Nat.Partrec.Code) :
    CodeTotal c ↔ ∀ n, ∃ k, boundedTotalityWitness ((c, n), k) = true := by
  simp only [CodeTotal, eval_dom_iff_bounded]

theorem closedNumericalTotal_has_bounded_form :
    ∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedNumericalTotal t ↔ ∀ n, ∃ k, boundedTotalityWitness ((f t, n), k) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  refine ⟨closedTotalityCode u, closedTotalityCode_primrec u, ?_⟩
  intro t
  exact (closedTotalityCode_correct u hu t).trans (codeTotal_iff_bounded _)

set_option backward.isDefEq.respectTransparency false in
/-- Every computable universal-existential normal form reduces to closed numerical totality. -/
theorem closedNumericalTotal_normalForm_hard
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ∃ f : Nat → Term, Primrec f ∧ ∀ a,
      ((∀ n, ∃ k, R ((a, n), k) = true) ↔ ClosedNumericalTotal (f a)) := by
  let S : Nat × Nat → Bool := fun p => R (p.1.unpair, p.2)
  have hS : Computable S := hR.comp ((Computable.unpair.comp Computable.fst).pair Computable.snd)
  have hs : Partrec (fun m : Nat => Nat.rfind (fun k => (S (m, k) : Part Bool))) :=
    Partrec.rfind hS.partrec.to₂
  have hs' : Nat.Partrec (fun m : Nat => Nat.rfind (fun k => (S (m, k) : Part Bool))) :=
    Partrec.nat_iff.1 hs
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hs'
  let f : Nat → Term := fun a => compileLambdaTotal (Nat.Partrec.Code.curry u a)
  have hf : Primrec f := primrec_compileLambdaTotal.comp
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id)
  refine ⟨f, hf, ?_⟩
  intro a
  have he (n : Nat) : numericalValue (f a) n =
      Nat.rfind (fun k => (R ((a, n), k) : Part Bool)) := by
    rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry, hu]
    simp [S]
  constructor
  · intro hp
    refine ⟨(compileLambdaTotal_sound _).1, ?_⟩
    intro n
    rw [he n, Nat.rfind_dom]
    obtain ⟨k, hk⟩ := hp n
    exact ⟨k, by simpa using hk, fun {_} _ => trivial⟩
  · intro hp n
    have hdom := hp.2 n
    rw [he n, Nat.rfind_dom] at hdom
    obtain ⟨k, hk, _⟩ := hdom
    exact ⟨k, by simpa using hk⟩

theorem closedNumericalTotal_normalForm_manyOne
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ManyOneReducible (fun a => ∀ n, ∃ k, R ((a, n), k) = true) ClosedNumericalTotal := by
  obtain ⟨f, hf, hc⟩ := closedNumericalTotal_normalForm_hard R hR
  exact ⟨f, hf.to_comp, hc⟩

/-- Complete for computable universal-existential normal forms under many-one reductions. -/
theorem closedNumericalTotal_normalForm_complete :
    (∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedNumericalTotal t ↔ ∀ n, ∃ k, boundedTotalityWitness ((f t, n), k) = true)) ∧
    ∀ R : (Nat × Nat) × Nat → Bool, Computable R →
      ManyOneReducible (fun a => ∀ n, ∃ k, R ((a, n), k) = true) ClosedNumericalTotal :=
  ⟨closedNumericalTotal_has_bounded_form, closedNumericalTotal_normalForm_manyOne⟩

#print axioms closedNumericalTotal_normalForm_complete
#print axioms closedNumericalTotal_normalForm_hard
#print axioms closedNumericalTotal_has_bounded_form
#print axioms codeTotal_iff_bounded
#print axioms boundedTotalityWitness_primrec
end LambdaTuring
