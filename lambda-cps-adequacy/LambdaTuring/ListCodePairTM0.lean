/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodePairCompiler
public meta import LambdaTuring.ListCodePairCompiler
public import LambdaTuring.TM2TM0Bridge
public meta import LambdaTuring.TM2TM0Bridge

@[expose] public section

namespace LambdaTuring

set_option linter.style.haveILetI false in
/-- The extended pair compiler reaches the same numerical results through
    Mathlib's encoded TM0 simulation, with exact absence of results. -/
theorem compileListCodePair_tm0_numerical_iff (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodePair c = some C) (n m : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ Nat.Partrec.Code.eval c n := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := (compileListCodePair_sound c C h) n
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
theorem compileListCodePair_lambda_tm0 (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodePair c = some C) (n m : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  rw [(compileLambdaTotal_sound c).2 n]
  exact compileListCodePair_tm0_numerical_iff c C h n m

set_option linter.style.haveILetI false in
theorem compileListCodePair_lambda_tm0_none (c : Nat.Partrec.Code)
    (C : Turing.ToPartrec.Code) (h : compileListCodePair c = some C) (n : Nat) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [Part.eq_none_iff]
  constructor
  · intro hnone m hm
    obtain ⟨out, hout, hdecode⟩ := (compileListCodePair_lambda_tm0 c C h n m).2 hm
    exact hnone ⟨m, out, hout, hdecode⟩
  · rintro hnone ⟨m, out, hout, hdecode⟩
    exact hnone m ((compileListCodePair_lambda_tm0 c C h n m).1 ⟨out, hout, hdecode⟩)

#print axioms compileListCodePair_tm0_numerical_iff
#print axioms compileListCodePair_lambda_tm0
#print axioms compileListCodePair_lambda_tm0_none
end LambdaTuring
