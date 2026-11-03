/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeUnaryOutput
public meta import LambdaTuring.ListCodeUnaryOutput

@[expose] public section

namespace LambdaTuring

def unaryOnesProgram (c : Nat.Partrec.Code) :=
  Machine.sequenceProgram simulatorInputPreprocessor (blockProgram (compileUnaryOutputCode c))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem mathTape_output_member_iff {states : Nat} (p : Machine.Program states)
    (t : Machine.Tape) (xs : List Machine.Symbol) (out : Turing.ListBlank Machine.Symbol)
    (ht : Machine.mathTape t = Turing.Tape.mk₁ xs) :
    (∃ d, Machine.Reaches p ⟨⟨0, by omega⟩, t⟩ d ∧ Machine.Halted p d ∧
      (Machine.mathTape d.tape).right₀ = out) ↔
    out ∈ Turing.TM0.eval (Machine.mathProgram p) xs := by
  letI : Inhabited (Fin (states + 1)) := ⟨0⟩
  have hinit : Machine.mathConfig (⟨⟨0, by omega⟩, t⟩ : Machine.Config states) =
      Turing.TM0.init xs := by
    simp [Machine.mathConfig, Turing.TM0.init, ht]
  change _ ↔ out ∈ (StateTransition.eval (Turing.TM0.step (Machine.mathProgram p))
    (Turing.TM0.init xs)).map (fun cfg => cfg.Tape.right₀)
  rw [← hinit, Machine.math_eval_configs]
  constructor
  · rintro ⟨d, hd, hh, he⟩
    apply (Part.mem_map_iff _).2
    refine ⟨Machine.mathConfig d, ?_, he⟩
    apply (Part.mem_map_iff _).2
    exact ⟨d, StateTransition.mem_eval.2 ⟨Machine.reaches_stateTransition.1 hd, hh⟩, rfl⟩
  · intro hout
    obtain ⟨cfg, hcfg, he⟩ := (Part.mem_map_iff _).1 hout
    obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).1 hcfg
    obtain ⟨hr, hh⟩ := StateTransition.mem_eval.1 hd
    exact ⟨d, Machine.reaches_stateTransition.2 hr, hh, he⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOnesProgram_output_shape (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    let C := compileUnaryOutputCode c
    let preSize := Machine.prefixLoopSize .mark .one prefixTail bitTail + 2 + 1
    ∃ (d : Machine.Config (BlockTM0StateCount C))
      (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)),
        Machine.Reaches (unaryOnesProgram c) (Machine.initial n) (Machine.sequenceRightConfig (n := preSize) d) ∧
        Machine.Halted (unaryOnesProgram c) (Machine.sequenceRightConfig (n := preSize) d) ∧
        (Machine.mathTape d.tape).right₀ = encodeBlankSide (Turing.TM2to1.addBottom L) ∧
        L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
          Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
            List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)) := by
  let C := compileUnaryOutputCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  obtain ⟨out, L, hout, heq, hshape⟩ := unaryOutput_mainTrack c n m hm
  have hblock : encodeBlankSide out ∈ Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [onesNumber n])) := by
    rw [blockProgram_encoded_eval, numberedMachine_eval]
    exact (Part.mem_map_iff _).2 ⟨out, hout, rfl⟩
  obtain ⟨mid, hpre, hhalt, htape⟩ := simulatorInputPreprocessor_correct n
  obtain ⟨d, hd, hdh, hdo⟩ :=
    (mathTape_output_member_iff (blockProgram C) mid.tape
      (encodeSimSymbols (tm0ListInput [onesNumber n])) (encodeBlankSide out) htape).2 hblock
  let preSize := Machine.prefixLoopSize .mark .one prefixTail bitTail + 2 + 1
  have hseq := (Machine.sequence_terminal_iff simulatorInputPreprocessor (blockProgram C)
    (Machine.initial n) mid hpre hhalt (Machine.sequenceRightConfig (n := preSize) d)).2 ⟨d, rfl, hd, hdh⟩
  refine ⟨d, L, ?_, ?_, ?_, hshape⟩
  · simpa [unaryOnesProgram, C, Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hseq.1
  · exact hseq.2
  · exact hdo.trans (congrArg encodeBlankSide heq.symm)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem mathTape_termination_iff {states : Nat} (p : Machine.Program states)
    (t : Machine.Tape) (xs : List Machine.Symbol)
    (ht : Machine.mathTape t = Turing.Tape.mk₁ xs) :
    (∃ d, Machine.Reaches p ⟨⟨0, by omega⟩, t⟩ d ∧ Machine.Halted p d) ↔
      (Turing.TM0.eval (Machine.mathProgram p) xs).Dom := by
  constructor
  · rintro ⟨d, hd, hh⟩
    apply Part.dom_iff_mem.2
    refine ⟨(Machine.mathTape d.tape).right₀, ?_⟩
    exact (mathTape_output_member_iff p t xs _ ht).1 ⟨d, hd, hh, rfl⟩
  · intro hdom
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨d, hd, hh, _⟩ := (mathTape_output_member_iff p t xs out ht).2 hout
    exact ⟨d, hd, hh⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOnesBlock_domain (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileUnaryOutputCode c
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (Turing.TM0.eval (Machine.mathProgram (blockProgram C))
      (encodeSimSymbols (tm0ListInput [onesNumber n]))).Dom ↔
        (numericalValue (compileLambdaTotal c) n).Dom := by
  let C := compileUnaryOutputCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  change (Turing.TM0.eval (Machine.mathProgram (blockProgram C))
    (encodeSimSymbols (tm0ListInput [onesNumber n]))).Dom ↔ _
  rw [blockProgram_encoded_eval, numberedMachine_eval]
  have h := tm0List_domain C [onesNumber n]
  rw [compileUnaryOutputCode_eval] at h
  rw [(compileLambdaTotal_sound c).2 n]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOnesProgram_terminates_iff (c : Nat.Partrec.Code) (n : Nat) :
    (∃ d, Machine.Reaches (unaryOnesProgram c) (Machine.initial n) d ∧
      Machine.Halted (unaryOnesProgram c) d) ↔
        (numericalValue (compileLambdaTotal c) n).Dom := by
  let C := compileUnaryOutputCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  obtain ⟨mid, hpre, hhalt, htape⟩ := simulatorInputPreprocessor_correct n
  have hs := Machine.sequence_observation_iff simulatorInputPreprocessor (blockProgram C)
    (Machine.initial n) mid hpre hhalt (fun _ => some 0) 0
  have ht := mathTape_termination_iff (blockProgram C) mid.tape
    (encodeSimSymbols (tm0ListInput [onesNumber n])) htape
  have hd := unaryOnesBlock_domain c n
  change (∃ d, Machine.Reaches (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C))
    (Machine.initial n) d ∧ Machine.Halted (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C)) d) ↔ _
  have hs' : (∃ d, Machine.Reaches (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C))
    (Machine.initial n) d ∧ Machine.Halted (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C)) d) ↔
      (∃ d, Machine.Reaches (blockProgram C) ⟨⟨0, by omega⟩, mid.tape⟩ d ∧ Machine.Halted (blockProgram C) d) := by
    simpa [Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hs
  exact hs'.trans (ht.trans hd)

theorem unaryOnesProgram_no_halt (c : Nat.Partrec.Code) (n : Nat) :
    (¬ ∃ d, Machine.Reaches (unaryOnesProgram c) (Machine.initial n) d ∧
      Machine.Halted (unaryOnesProgram c) d) ↔
        numericalValue (compileLambdaTotal c) n = Part.none := by
  constructor
  · intro h
    apply Part.eq_none_iff.2
    intro m hm
    exact h ((unaryOnesProgram_terminates_iff c n).2 (Part.dom_iff_mem.2 ⟨m, hm⟩))
  · intro h hterm
    have hd := (unaryOnesProgram_terminates_iff c n).1 hterm
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 hd
    exact (Part.eq_none_iff.1 h) m hm

#print axioms unaryOnesProgram_output_shape
#print axioms unaryOnesProgram_terminates_iff
#print axioms unaryOnesProgram_no_halt
end LambdaTuring
