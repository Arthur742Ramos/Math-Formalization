/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.FiniteOrbit
public meta import LambdaTuring.FiniteOrbit

@[expose] public section
namespace LambdaTuring

/-- Decode syntax with a fixed open-term fallback. Membership below also checks
canonical re-encoding, so invalid or noncanonical codes cannot be accepted. -/
def decodedSyntax (n : Nat) : Term :=
  (executableTermDecode n).getD (.var 0)

def codedClosedZero (n : Nat) : Prop :=
  n = executableTermEncode (decodedSyntax n) ∧ closedNumeralAtZero 0 (decodedSyntax n)

theorem decodedSyntax_primrec : Primrec decodedSyntax := by
  have h : Primrec (fun n : Nat => (Encodable.decode n : Option Term).getD (.var 0)) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const _)
  exact h.of_eq (fun n => by simp [decodedSyntax, executableTermDecode_eq])

theorem codedClosedZero_encode (t : Term) :
    codedClosedZero (executableTermEncode t) ↔ closedNumeralAtZero 0 t := by
  simp [codedClosedZero, decodedSyntax, executableTermDecode_encode]

theorem codedClosedZero_exact (n : Nat) :
    codedClosedZero n ↔ ∃ t, executableTermEncode t = n ∧ closedNumeralAtZero 0 t := by
  constructor
  · rintro ⟨he, hz⟩
    exact ⟨decodedSyntax n, he.symm, hz⟩
  · rintro ⟨t, rfl, hz⟩
    exact (codedClosedZero_encode t).2 hz

theorem codedClosedZero_re : REPred codedClosedZero := by
  have hterm : Computable decodedSyntax := decodedSyntax_primrec.to_comp
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hvalid : Computable (fun n : Nat => decide (n = executableTermEncode (decodedSyntax n))) :=
    (Primrec.eq : PrimrecRel (fun x y : Nat => x = y)).decide.to_comp.comp
      Computable.id (henc.comp hterm)
  have hclosed : Partrec (fun n : Nat =>
      Part.assert (closedNumeralAtZero 0 (decodedSyntax n)) fun _ => Part.some ()) :=
    (closedNumeralAtZero_re 0).comp hterm
  have hp := Partrec.cond hvalid hclosed Partrec.none
  apply hp.dom_re.of_eq
  intro n
  change (bif decide (n = executableTermEncode (decodedSyntax n)) then
    Part.assert (closedNumeralAtZero 0 (decodedSyntax n)) (fun _ => Part.some ())
    else Part.none).Dom ↔ codedClosedZero n
  by_cases he : n = executableTermEncode (decodedSyntax n)
  · have hb : decide (n = executableTermEncode (decodedSyntax n)) = true := decide_eq_true he
    simp only [hb, Bool.cond_true]
    change (∃ _ : closedNumeralAtZero 0 (decodedSyntax n), True) ↔ codedClosedZero n
    exact ⟨fun ⟨hz, _⟩ => ⟨he, hz⟩, fun h => ⟨h.2, trivial⟩⟩
  · have hb : decide (n = executableTermEncode (decodedSyntax n)) = false := decide_eq_false he
    simp only [hb, Bool.cond_false]
    change False ↔ codedClosedZero n
    exact ⟨False.elim, fun h => he h.1⟩

/-- Canonical code of a recursive program together with its numerical input. -/
def decodedCodeInput (n : Nat) : Nat.Partrec.Code × Nat :=
  (Encodable.decode n : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)

def codedHalting (n : Nat) : Prop :=
  n = Encodable.encode (decodedCodeInput n) ∧
    (Nat.Partrec.Code.eval (decodedCodeInput n).1 (decodedCodeInput n).2).Dom

theorem decodedCodeInput_primrec : Primrec decodedCodeInput :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

theorem codedHalting_encode (p : Nat.Partrec.Code × Nat) :
    codedHalting (Encodable.encode p) ↔ (Nat.Partrec.Code.eval p.1 p.2).Dom := by
  have hd : decodedCodeInput (Encodable.encode p) = p := by
    unfold decodedCodeInput
    rw [Encodable.encodek]
    rfl
  change (Encodable.encode p = Encodable.encode (decodedCodeInput (Encodable.encode p)) ∧ _) ↔ _
  rw [hd]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

theorem codedHalting_re : REPred codedHalting := by
  have hd : Computable decodedCodeInput := decodedCodeInput_primrec.to_comp
  have hvalid : Computable (fun n : Nat => decide (n = Encodable.encode (decodedCodeInput n))) :=
    (Primrec.eq : PrimrecRel (fun x y : Nat => x = y)).decide.to_comp.comp
      Computable.id (Computable.encode.comp hd)
  have heval : Partrec (fun n : Nat => Nat.Partrec.Code.eval
      (decodedCodeInput n).1 (decodedCodeInput n).2) :=
    Nat.Partrec.Code.eval_part.comp (Computable.fst.comp hd) (Computable.snd.comp hd)
  have hp := Partrec.cond hvalid heval Partrec.none
  apply hp.dom_re.of_eq
  intro n
  by_cases he : n = Encodable.encode (decodedCodeInput n)
  · have hb : decide (n = Encodable.encode (decodedCodeInput n)) = true := decide_eq_true he
    simp only [hb, Bool.cond_true]
    exact ⟨fun h => ⟨he, h⟩, And.right⟩
  · have hb : decide (n = Encodable.encode (decodedCodeInput n)) = false := decide_eq_false he
    simp only [hb, Bool.cond_false]
    change False ↔ codedHalting n
    exact ⟨False.elim, fun h => he h.1⟩

theorem codedHalting_exact (n : Nat) :
    codedHalting n ↔ ∃ p : Nat.Partrec.Code × Nat,
      Encodable.encode p = n ∧ (Nat.Partrec.Code.eval p.1 p.2).Dom := by
  constructor
  · rintro ⟨he, hh⟩
    exact ⟨decodedCodeInput n, he.symm, hh⟩
  · rintro ⟨p, rfl, hh⟩
    exact (codedHalting_encode p).2 hh

/-- Invalid syntax codes are outside the concrete lambda language. -/
theorem codedClosedZero_invalid (n : Nat) (h : executableTermDecode n = none) :
    ¬ codedClosedZero n := by
  intro hz
  have hd := executableTermDecode_encode (decodedSyntax n)
  rw [← hz.1, h] at hd
  contradiction

/-- Invalid code-input encodings are outside the canonical halting language. -/
theorem codedHalting_invalid (n : Nat)
    (h : (Encodable.decode n : Option (Nat.Partrec.Code × Nat)) = none) :
    ¬ codedHalting n := by
  intro hh
  have hd := Encodable.encodek (decodedCodeInput n)
  rw [← hh.1, h] at hd
  contradiction

/-- Every r.e. numerical predicate has an injective primitive-recursive
reduction to the canonical code-input halting language. The recursive program
for the fixed predicate is selected by existence. -/
theorem codedHalting_oneOne_complete (p : Nat → Prop) (hp : REPred p) :
    ∃ f : Nat → Nat, Primrec f ∧ Function.Injective f ∧
      ∀ n, p n ↔ codedHalting (f n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hdom (n : Nat) : (Nat.Partrec.Code.eval c (Encodable.encode n)).Dom ↔ p n := by
    rw [hc]
    simp [Part.assert]
  let f : Nat → Nat := fun n => Encodable.encode (c, Encodable.encode n)
  have hf : Primrec f := Primrec.encode.comp ((Primrec.const c).pair Primrec.encode)
  have hi : Function.Injective f := by
    intro a b hab
    have hpair : (c, Encodable.encode a) = (c, Encodable.encode b) :=
      Encodable.encode_injective hab
    exact Encodable.encode_injective (congrArg Prod.snd hpair)
  exact ⟨f, hf, hi, fun n => (hdom n).symm.trans
    (codedHalting_encode (c, Encodable.encode n)).symm⟩

/-- The canonical lambda zero-result language receives every r.e. numerical
language by an injective primitive-recursive map of natural-number codes. -/
theorem codedClosedZero_oneOne_complete (p : Nat → Prop) (hp : REPred p) :
    ∃ f : Nat → Nat, Primrec f ∧ Function.Injective f ∧
      ∀ n, p n ↔ codedClosedZero (f n) := by
  obtain ⟨g, hg, hgi, hgr⟩ := closed_zero_oneOne_complete p hp
  let f : Nat → Nat := fun n => executableTermEncode (g n)
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  have hi : Function.Injective f := by
    intro a b hab
    apply hgi
    apply Encodable.encode_injective
    change executableTermEncode (g a) = executableTermEncode (g b) at hab
    simpa only [executableTermEncode_eq] using hab
  exact ⟨f, henc.comp hg, hi, fun n => (hgr n).trans (codedClosedZero_encode (g n)).symm⟩

/-- The canonical recursive-code halting language and the canonical codes of
closed lambda programs returning zero are computably isomorphic. -/
theorem codedHalting_closedZero_isomorphism :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ n, codedHalting n ↔ codedClosedZero (e n) := by
  obtain ⟨f, hf, hfi, hfr⟩ := codedClosedZero_oneOne_complete codedHalting codedHalting_re
  obtain ⟨g, hg, hgi, hgr⟩ := codedHalting_oneOne_complete codedClosedZero codedClosedZero_re
  exact computable_permutation_of_oneOneEquiv codedHalting codedClosedZero
    ⟨⟨f, hf.to_comp, hfi, hfr⟩, ⟨g, hg.to_comp, hgi, hgr⟩⟩

/-- On every actual encoded code-input pair, the isomorphism transports its
halting question to the closed lambda zero-result language. -/
theorem codeInput_closedZero_permutation :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ c n, codedClosedZero (e (Encodable.encode (c, n))) ↔
        (Nat.Partrec.Code.eval c n).Dom := by
  obtain ⟨e, he, hei, h⟩ := codedHalting_closedZero_isomorphism
  refine ⟨e, he, hei, ?_⟩
  intro c n
  exact (h (Encodable.encode (c, n))).symm.trans (codedHalting_encode (c, n))

#print axioms codedClosedZero_re
#print axioms codedClosedZero_exact
#print axioms codedHalting_re
#print axioms codedHalting_exact
#print axioms codedClosedZero_invalid
#print axioms codedHalting_invalid
#print axioms codedHalting_oneOne_complete
#print axioms codedClosedZero_oneOne_complete
#print axioms codedHalting_closedZero_isomorphism
#print axioms codeInput_closedZero_permutation
end LambdaTuring
