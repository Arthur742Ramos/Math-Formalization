/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeMinimizationCompiler
public meta import LambdaTuring.ListCodeMinimizationCompiler

@[expose] public section

namespace LambdaTuring

/-- A structural translation of every numeric partial-recursive code into
    Mathlib's executable list-code language. -/
def compileListCodeTotal : Nat.Partrec.Code → Turing.ToPartrec.Code
  | .zero => .zero
  | .succ => .succ
  | .left => listCodeUnpairLeft
  | .right => listCodeUnpairRight
  | .pair f g => .comp listCodeNatPair (listCodeTuple (compileListCodeTotal f) (compileListCodeTotal g))
  | .comp f g => .comp (compileListCodeTotal f) (compileListCodeTotal g)
  | .prec f g => listCodeRecursion (compileListCodeTotal f) (compileListCodeTotal g)
  | .rfind' g => listCodeMinimize (compileListCodeTotal g)

theorem compileListCodeTotal_sound (c : Nat.Partrec.Code) :
    ListCodeRepresents (compileListCodeTotal c) (Nat.Partrec.Code.eval c) := by
  induction c with
  | zero => exact listCode_zero
  | succ => exact listCode_succ
  | left => exact listCode_left
  | right => exact listCode_right
  | comp f g ihf ihg =>
    have heval : Nat.Partrec.Code.eval (.comp f g) =
        (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
      funext n
      exact Part.bind_eq_bind _ _
    rw [heval]
    exact listCode_comp ihf ihg
  | pair f g ihf ihg =>
    have heval : Nat.Partrec.Code.eval (.pair f g) =
        (fun n => (Nat.Partrec.Code.eval f n).bind
          (fun a => (Nat.Partrec.Code.eval g n).map (Nat.pair a))) := by
      rw [codePair_eval]
      funext n
      simp [numericalPairBind, Part.bind_some_eq_map]
    rw [heval]
    exact listCode_pair_of_encoder ihf ihg listCodeNatPair_eval
  | prec f g ihf ihg => exact listCodeRecursion_represents ihf ihg
  | rfind' g ih => exact listCodeMinimize_represents ih

set_option linter.style.haveILetI false in
theorem compileListCodeTotal_lambda_tm0 (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileListCodeTotal c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := (compileListCodeTotal_sound c) n
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
theorem compileListCodeTotal_lambda_tm0_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  let C := compileListCodeTotal c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [Part.eq_none_iff]
  constructor
  · intro hnone m hm
    obtain ⟨out, hout, hdecode⟩ := (compileListCodeTotal_lambda_tm0 c n m).2 hm
    exact hnone ⟨m, out, hout, hdecode⟩
  · rintro hnone ⟨m, out, hout, hdecode⟩
    exact hnone m ((compileListCodeTotal_lambda_tm0 c n m).1 ⟨out, hout, hdecode⟩)

theorem undefined_search_test_none (n : Nat) :
    Nat.Partrec.Code.eval (.rfind' bottomCode) n = Part.none := by
  apply Part.eq_none_iff.2
  intro r hr
  change r ∈ (Nat.rfind (fun k =>
    (Nat.Partrec.Code.eval bottomCode (Nat.pair n.unpair.1 (k+n.unpair.2))).map
      (fun x => x = 0))).map (fun k => k+n.unpair.2) at hr
  obtain ⟨k, hk, _⟩ := (Part.mem_map_iff _).1 hr
  have hz := (Nat.mem_rfind.1 hk).1
  rw [bottomCode_eval] at hz
  simp at hz

set_option linter.style.haveILetI false in
theorem compiledTotal_undefined_search_no_output (n : Nat) :
    let C := compileListCodeTotal (.rfind' bottomCode)
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    ¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m := by
  apply (compileListCodeTotal_lambda_tm0_none (.rfind' bottomCode) n).2
  rw [(compileLambdaTotal_sound _).2, undefined_search_test_none]

set_option linter.style.haveILetI false in
theorem compiledTotal_infinite_search_no_output (n : Nat) :
    let C := compileListCodeTotal bottomCode
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    ¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m := by
  apply (compileListCodeTotal_lambda_tm0_none bottomCode n).2
  rw [(compileLambdaTotal_sound _).2, bottomCode_eval]

#print axioms compileListCodeTotal_sound
#print axioms compileListCodeTotal_lambda_tm0
#print axioms compileListCodeTotal_lambda_tm0_none
#print axioms compiledTotal_undefined_search_no_output
#print axioms compiledTotal_infinite_search_no_output
end LambdaTuring
