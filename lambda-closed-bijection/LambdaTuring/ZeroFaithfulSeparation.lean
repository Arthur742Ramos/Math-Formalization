/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.CodedIsomorphism
public meta import LambdaTuring.CodedIsomorphism

@[expose] public section
namespace LambdaTuring

/-- The exact one-bit condition of the closed-object bijection. -/
def ZeroObservationFaithful (F : Nat.Partrec.Code × Nat → Term) : Prop :=
  ∀ p, (Nat.Partrec.Code.eval p.1 p.2).Dom ↔ closedNumeralAtZero 0 (F p)

/-- Distinct closed programs computing each positive constant function. -/
def paddedPositive (n : Nat) : Term :=
  syntaxPadding (n, compileLambdaTotal (.const (n + 1)))

theorem paddedPositive_primrec : Primrec paddedPositive :=
  syntaxPadding_primrec.comp (Primrec.id.pair
    (primrec_compileLambdaTotal.comp (Nat.Partrec.Code.primrec_const.comp Primrec.succ)))

theorem paddedPositive_injective : Function.Injective paddedPositive := by
  intro a b h
  have hp := syntaxPadding_injective h
  exact congrArg Prod.fst hp

theorem paddedPositive_closed (n : Nat) : Scoped 0 (paddedPositive n) :=
  syntaxPadding_closed n (compileLambdaTotal_sound (.const (n + 1))).1

theorem paddedPositive_result (n x m : Nat) :
    NumericalResult (paddedPositive n) x m ↔ m = n + 1 := by
  rw [← mem_numericalValue_iff]
  change m ∈ numericalValue (syntaxPadding (n, compileLambdaTotal (.const (n + 1)))) x ↔ m = n + 1
  rw [syntaxPadding_numericalValue, (compileLambdaTotal_sound (.const (n + 1))).2 x,
    Nat.Partrec.Code.eval_const]
  simp

/-- An injective family of source computations returning every positive value. -/
def sourcePositive (n : Nat) : Nat.Partrec.Code × Nat := (.const (n + 1), n)

theorem sourcePositive_primrec : Primrec sourcePositive :=
  (Nat.Partrec.Code.primrec_const.comp Primrec.succ).pair Primrec.id

theorem sourcePositive_injective : Function.Injective sourcePositive := by
  intro a b h
  exact congrArg Prod.snd h

/-- A map obeying the zero-observation criterion fails to preserve values on
infinitely many source computations returning distinct positive values. -/
theorem zeroFaithful_halt_mismatch (F : Nat.Partrec.Code × Nat → Term)
    (hF : ZeroObservationFaithful F) :
    ∃ family : Nat → Nat.Partrec.Code × Nat, Primrec family ∧ Function.Injective family ∧
      ∀ n, (n + 1) ∈ Nat.Partrec.Code.eval (family n).1 (family n).2 ∧
        NumericalResult (F (family n)) 0 0 ∧ ¬ NumericalResult (F (family n)) 0 (n + 1) := by
  refine ⟨sourcePositive, sourcePositive_primrec, sourcePositive_injective, ?_⟩
  intro n
  have hmem : (n + 1) ∈ Nat.Partrec.Code.eval (sourcePositive n).1 (sourcePositive n).2 := by
    simp [sourcePositive, Nat.Partrec.Code.eval_const]
  have hd : (Nat.Partrec.Code.eval (sourcePositive n).1 (sourcePositive n).2).Dom :=
    (Part.dom_iff_mem).2 ⟨n + 1, hmem⟩
  have hz : NumericalResult (F (sourcePositive n)) 0 0 := ((hF _).1 hd).2
  refine ⟨hmem, hz, ?_⟩
  intro hone
  have heq := numeral_result_unique hz hone
  omega

/-- Surjectivity onto closed terms forces infinitely many nonhalting source
computations to map to programs computing all positive constant functions. -/
theorem zeroFaithful_nonhalt_mismatch (F : Nat.Partrec.Code × Nat → Term)
    (G : Term → Nat.Partrec.Code × Nat) (hG : Computable G)
    (hF : ZeroObservationFaithful F)
    (hsurj : ∀ t, Scoped 0 t → F (G t) = t) :
    ∃ family : Nat → Nat.Partrec.Code × Nat, Computable family ∧ Function.Injective family ∧
      ∀ n, ¬ (Nat.Partrec.Code.eval (family n).1 (family n).2).Dom ∧
        ∀ x m, NumericalResult (F (family n)) x m ↔ m = n + 1 := by
  let family : Nat → Nat.Partrec.Code × Nat := fun n => G (paddedPositive n)
  have hc : Computable family := hG.comp paddedPositive_primrec.to_comp
  have hi : Function.Injective family := by
    intro a b hab
    apply paddedPositive_injective
    have h := congrArg F hab
    simpa only [family, hsurj _ (paddedPositive_closed _)] using h
  refine ⟨family, hc, hi, ?_⟩
  intro n
  have he : F (family n) = paddedPositive n := hsurj _ (paddedPositive_closed n)
  have hone : NumericalResult (paddedPositive n) 0 (n + 1) :=
    (paddedPositive_result n 0 (n + 1)).2 rfl
  constructor
  · intro hd
    have hz : NumericalResult (paddedPositive n) 0 0 := by
      have hz' := ((hF (family n)).1 hd).2
      simpa only [he] using hz'
    have heq := numeral_result_unique hz hone
    omega
  · intro x m
    simpa only [he] using paddedPositive_result n x m

/-- Zero-faithful encodings cannot preserve all numerical result values even
at input zero, independent of whether they are computable or surjective. -/
theorem no_zeroFaithful_value_preservation (F : Nat.Partrec.Code × Nat → Term)
    (hF : ZeroObservationFaithful F) :
    ¬ ∀ p m, NumericalResult (F p) 0 m ↔ m ∈ Nat.Partrec.Code.eval p.1 p.2 := by
  intro hall
  obtain ⟨family, _, _, h⟩ := zeroFaithful_halt_mismatch F hF
  have hzero := (hall (family 0) 0).1 ((h 0).2.1)
  have hone := (h 0).1
  have heq := Part.mem_unique hzero hone
  omega

/-- The previously constructed closed-object bijection has both infinite
mismatch families; no value-preserving conclusion is implied. -/
theorem closedBijection_has_two_sided_mismatches :
    ∃ F : Nat.Partrec.Code × Nat → Term, ∃ G : Term → Nat.Partrec.Code × Nat,
      Computable F ∧ Computable G ∧
      (∀ p, Scoped 0 (F p)) ∧
      (∀ p, G (F p) = p) ∧
      (∀ t, Scoped 0 t → F (G t) = t) ∧
      ZeroObservationFaithful F ∧
      (∃ family : Nat → Nat.Partrec.Code × Nat, Primrec family ∧ Function.Injective family ∧
        ∀ n, (n + 1) ∈ Nat.Partrec.Code.eval (family n).1 (family n).2 ∧
          NumericalResult (F (family n)) 0 0 ∧ ¬ NumericalResult (F (family n)) 0 (n + 1)) ∧
      (∃ family : Nat → Nat.Partrec.Code × Nat, Computable family ∧ Function.Injective family ∧
        ∀ n, ¬ (Nat.Partrec.Code.eval (family n).1 (family n).2).Dom ∧
          ∀ x m, NumericalResult (F (family n)) x m ↔ m = n + 1) := by
  obtain ⟨F, G, hFc, hGc, hclosed, hleft, hright, hfaithful⟩ := codeInput_closedTerm_bijection
  exact ⟨F, G, hFc, hGc, hclosed, hleft, hright, hfaithful,
    zeroFaithful_halt_mismatch F hfaithful, zeroFaithful_nonhalt_mismatch F G hGc hfaithful hright⟩

#print axioms paddedPositive_result
#print axioms zeroFaithful_halt_mismatch
#print axioms zeroFaithful_nonhalt_mismatch
#print axioms no_zeroFaithful_value_preservation
#print axioms closedBijection_has_two_sided_mismatches
end LambdaTuring
