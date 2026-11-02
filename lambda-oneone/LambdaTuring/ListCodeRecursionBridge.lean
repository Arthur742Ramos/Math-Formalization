/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeRecursionCompiler
public meta import LambdaTuring.ListCodeRecursionCompiler

@[expose] public section

namespace LambdaTuring

/-- The executable fragment handles strict primitive recursion as well as
    projections, compositions, and pairings of supported codes. -/
def compileListCodeRecursion : Nat.Partrec.Code → Option Turing.ToPartrec.Code
  | .left => some listCodeUnpairLeft
  | .right => some listCodeUnpairRight
  | .pair f g => do
      let F ← compileListCodeRecursion f
      let G ← compileListCodeRecursion g
      pure (.comp listCodeNatPair (listCodeTuple F G))
  | .prec f g => do
      let F ← compileListCodeRecursion f
      let G ← compileListCodeRecursion g
      pure (listCodeRecursion F G)
  | .comp f g => do
      let F ← compileListCodeRecursion f
      let G ← compileListCodeRecursion g
      pure (.comp F G)
  | c => compileListCode c

theorem compileListCodeRecursion_sound (c : Nat.Partrec.Code) (C : Turing.ToPartrec.Code)
    (h : compileListCodeRecursion c = some C) : ListCodeRepresents C (Nat.Partrec.Code.eval c) := by
  induction c generalizing C with
  | zero => exact compileListCode_sound .zero C h
  | succ => exact compileListCode_sound .succ C h
  | left =>
    have hC : listCodeUnpairLeft = C := by simpa [compileListCodeRecursion] using h
    subst C
    exact listCode_left
  | right =>
    have hC : listCodeUnpairRight = C := by simpa [compileListCodeRecursion] using h
    subst C
    exact listCode_right
  | prec f g ihf ihg =>
    cases hf : compileListCodeRecursion f with
    | none => simp [compileListCodeRecursion, hf] at h
    | some F =>
      cases hg : compileListCodeRecursion g with
      | none => simp [compileListCodeRecursion, hf, hg] at h
      | some G =>
        have heq : listCodeRecursion F G = C := by
          simpa [compileListCodeRecursion, hf, hg] using h
        subst C
        exact listCodeRecursion_represents (ihf F hf) (ihg G hg)
  | rfind' f ih => exact compileListCode_sound (.rfind' f) C h
  | comp f g ihf ihg =>
    cases hf : compileListCodeRecursion f with
    | none => simp [compileListCodeRecursion, hf] at h
    | some F =>
      cases hg : compileListCodeRecursion g with
      | none => simp [compileListCodeRecursion, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp F G = C := by
          simpa [compileListCodeRecursion, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.comp f g) =
            (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
          funext n
          exact Part.bind_eq_bind _ _
        rw [heval]
        exact listCode_comp (ihf F hf) (ihg G hg)
  | pair f g ihf ihg =>
    cases hf : compileListCodeRecursion f with
    | none => simp [compileListCodeRecursion, hf] at h
    | some F =>
      cases hg : compileListCodeRecursion g with
      | none => simp [compileListCodeRecursion, hf, hg] at h
      | some G =>
        have heq : Turing.ToPartrec.Code.comp listCodeNatPair (listCodeTuple F G) = C := by
          simpa [compileListCodeRecursion, hf, hg] using h
        subst C
        have heval : Nat.Partrec.Code.eval (.pair f g) =
            (fun n => (Nat.Partrec.Code.eval f n).bind
              (fun a => (Nat.Partrec.Code.eval g n).map (Nat.pair a))) := by
          rw [codePair_eval]
          funext n
          simp [numericalPairBind, Part.bind_some_eq_map]
        rw [heval]
        exact listCode_pair_of_encoder (ihf F hf) (ihg G hg) listCodeNatPair_eval

inductive ListCodeRecursionSupported : Nat.Partrec.Code → Prop where
  | zero : ListCodeRecursionSupported .zero
  | succ : ListCodeRecursionSupported .succ
  | left : ListCodeRecursionSupported .left
  | right : ListCodeRecursionSupported .right
  | bottom : ListCodeRecursionSupported bottomCode
  | comp {f g} : ListCodeRecursionSupported f → ListCodeRecursionSupported g → ListCodeRecursionSupported (.comp f g)
  | pair {f g} : ListCodeRecursionSupported f → ListCodeRecursionSupported g → ListCodeRecursionSupported (.pair f g)
  | prec {f g} : ListCodeRecursionSupported f → ListCodeRecursionSupported g → ListCodeRecursionSupported (.prec f g)

theorem compileListCodeRecursion_complete {c : Nat.Partrec.Code} (hc : ListCodeRecursionSupported c) :
    ∃ C, compileListCodeRecursion c = some C := by
  induction hc with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨listCodeUnpairLeft, rfl⟩
  | right => exact ⟨listCodeUnpairRight, rfl⟩
  | bottom => exact ⟨listCodeBottom, by simp [compileListCodeRecursion, compileListCode, bottomCode]⟩
  | @comp f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp F G, by simp [compileListCodeRecursion, hF, hG]⟩
  | @pair f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨.comp listCodeNatPair (listCodeTuple F G), by simp [compileListCodeRecursion, hF, hG]⟩

  | @prec f g _ _ ihf ihg =>
    obtain ⟨F, hF⟩ := ihf
    obtain ⟨G, hG⟩ := ihg
    exact ⟨listCodeRecursion F G, by simp [compileListCodeRecursion, hF, hG]⟩

set_option linter.style.haveILetI false in
theorem compileListCodeRecursion_lambda_tm0 (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodeRecursion c = some C) (n m : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := (compileListCodeRecursion_sound c C h) n
  rw [(compileLambdaTotal_sound c).2 n]
  constructor
  · rintro ⟨out, hout, hdecode⟩
    have hd : (C.eval [n]).Dom := (tm0List_domain C [n]).1 (Part.dom_iff_mem.2 ⟨out, hout⟩)
    obtain ⟨ys, hys⟩ := Part.dom_iff_mem.1 hd
    rw [hrep] at hys
    obtain ⟨k, hk, hys⟩ := (Part.mem_map_iff _).1 hys
    subst ys
    have hstack := tm0List_output_stack C [n] [k] out hout
      (by rw [hrep]; exact (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩)
    simp only [tm0DecodedNumber, hstack, decodeSingleton_trList, Option.some.injEq] at hdecode
    simpa [hdecode] using hk
  · intro hm
    have hc : [m] ∈ C.eval [n] := by
      rw [hrep]
      exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
    have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n])).Dom :=
      (tm0List_domain C [n]).2 (Part.dom_iff_mem.2 ⟨[m], hc⟩)
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
    refine ⟨out, hout, ?_⟩
    unfold tm0DecodedNumber
    rw [tm0List_output_stack C [n] [m] out hout hc]
    exact decodeSingleton_trList m

set_option linter.style.haveILetI false in
theorem compileListCodeRecursion_lambda_tm0_none (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodeRecursion c = some C) (n : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [Part.eq_none_iff]
  constructor
  · intro hnone m hm
    obtain ⟨out, hout, hdecode⟩ := (compileListCodeRecursion_lambda_tm0 c C h n m).2 hm
    exact hnone ⟨m, out, hout, hdecode⟩
  · rintro hnone ⟨m, out, hout, hdecode⟩
    exact hnone m ((compileListCodeRecursion_lambda_tm0 c C h n m).1 ⟨out, hout, hdecode⟩)

theorem codeRecursion_bottom_step_none (a : Nat) :
    Nat.Partrec.Code.eval (.prec .zero bottomCode) (Nat.pair a 1) = Part.none := by
  rw [Nat.Partrec.Code.eval_prec_succ, Nat.Partrec.Code.eval_prec_zero]
  simp [bottomCode_eval, Nat.Partrec.Code.eval, Part.bind_eq_bind]
  change (Part.some 0).bind (fun _ => Part.none) = Part.none
  exact Part.bind_some _ _

set_option linter.style.haveILetI false in
/-- A defined base with an undefined first recursive step has no numerical
    output in the compiled machine. -/
theorem compiledRecursion_bottom_step_no_output (a : Nat) :
    ∃ C, compileListCodeRecursion (.prec .zero bottomCode) = some C ∧
      letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
      ¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C)
        (tm0ListInput [Nat.pair a 1]) ∧ tm0DecodedNumber out = some m := by
  obtain ⟨C, hC⟩ := compileListCodeRecursion_complete
    (ListCodeRecursionSupported.prec .zero .bottom)
  refine ⟨C, hC, ?_⟩
  apply (compileListCodeRecursion_lambda_tm0_none _ C hC _).2
  rw [(compileLambdaTotal_sound _).2, codeRecursion_bottom_step_none]

#print axioms compileListCodeRecursion_sound
#print axioms compileListCodeRecursion_complete
#print axioms compileListCodeRecursion_lambda_tm0
#print axioms compileListCodeRecursion_lambda_tm0_none
#print axioms compiledRecursion_bottom_step_no_output
end LambdaTuring
