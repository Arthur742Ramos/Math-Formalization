/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeUnaryRecovery
public meta import LambdaTuring.ListCodeUnaryRecovery
public import LambdaTuring.BlockTapeDecoder
public meta import LambdaTuring.BlockTapeDecoder

@[expose] public section

namespace LambdaTuring

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem recoveredRaw_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileRecoveredListCode c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    (∃ out, out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileRecoveredListCode c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  have hrep := compileRecoveredListCode_eval c n
  rw [(compileLambdaTotal_sound c).2 n]
  constructor
  · rintro ⟨out, hout, hdecode⟩
    have hd : (C.eval [onesNumber n]).Dom :=
      (tm0List_domain C [onesNumber n]).1 (Part.dom_iff_mem.2 ⟨out, hout⟩)
    obtain ⟨ys, hys⟩ := Part.dom_iff_mem.1 hd
    rw [hrep] at hys
    obtain ⟨k, hk, hys⟩ := (Part.mem_map_iff _).1 hys
    subst ys
    have hstack := tm0List_output_stack C [onesNumber n] [k] out hout
      (by rw [hrep]; exact (Part.mem_map_iff _).2 ⟨k, hk, rfl⟩)
    simp only [tm0DecodedNumber, hstack, decodeSingleton_trList, Option.some.injEq] at hdecode
    simpa [hdecode] using hk
  · intro hm
    have hc : [m] ∈ C.eval [onesNumber n] := by
      rw [hrep]
      exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
    have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n])).Dom :=
      (tm0List_domain C [onesNumber n]).2 (Part.dom_iff_mem.2 ⟨[m], hc⟩)
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
    refine ⟨out, hout, ?_⟩
    unfold tm0DecodedNumber
    rw [tm0List_output_stack C [onesNumber n] [m] out hout hc]
    exact decodeSingleton_trList m

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem recoveredBlock_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileRecoveredListCode c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (∃ out, out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [onesNumber n])) ∧ blockDecodedNumber out = some m) ↔
      m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileRecoveredListCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  change (∃ out, out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
    (encodeSimSymbols (tm0ListInput [onesNumber n])) ∧ blockDecodedNumber out = some m) ↔
      m ∈ numericalValue (compileLambdaTotal c) n
  rw [blockProgram_encoded_eval, numberedMachine_eval]
  constructor
  · rintro ⟨out, hout, hd⟩
    obtain ⟨sourceOut, hs, he⟩ := (Part.mem_map_iff _).1 hout
    subst out
    apply (recoveredRaw_lambda_result c n m).1
    exact ⟨sourceOut, hs, by simpa [blockDecodedNumber, decodeBlockSide_encoded] using hd⟩
  · intro hm
    obtain ⟨sourceOut, hs, hd⟩ := (recoveredRaw_lambda_result c n m).2 hm
    refine ⟨encodeBlankSide sourceOut, (Part.mem_map_iff _).2 ⟨sourceOut, hs, rfl⟩, ?_⟩
    simpa [blockDecodedNumber, decodeBlockSide_encoded] using hd

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem recoveredBlock_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileRecoveredListCode c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [onesNumber n])) ∧ blockDecodedNumber out = some m) ↔
      numericalValue (compileLambdaTotal c) n = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro h m hm
    obtain ⟨out, hout, hd⟩ := (recoveredBlock_lambda_result c n m).2 hm
    exact h ⟨m, out, hout, hd⟩
  · rintro h ⟨m, out, hout, hd⟩
    exact h m ((recoveredBlock_lambda_result c n m).1 ⟨out, hout, hd⟩)

#print axioms recoveredBlock_lambda_result
#print axioms recoveredBlock_lambda_none
end LambdaTuring
