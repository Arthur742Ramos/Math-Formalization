/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryRecoveryBridge
public meta import LambdaTuring.UnaryRecoveryBridge
public import LambdaTuring.MachineSequenceExact
public meta import LambdaTuring.MachineSequenceExact

@[expose] public section

namespace LambdaTuring

/-- Public unary input followed by the block simulator with source-level
input recovery. Its final observation is still the block decoder. -/
def unaryCompiledProgram (c : Nat.Partrec.Code) :=
  Machine.sequenceProgram simulatorInputPreprocessor (blockProgram (compileRecoveredListCode c))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem mathTape_block_observation_iff {states : Nat} (p : Machine.Program states)
    (t : Machine.Tape) (xs : List Machine.Symbol) (m : Nat)
    (ht : Machine.mathTape t = Turing.Tape.mk₁ xs) :
    (∃ d, Machine.Reaches p ⟨⟨0, by omega⟩, t⟩ d ∧ Machine.Halted p d ∧
      blockDecodedNumber (Machine.mathTape d.tape).right₀ = some m) ↔
    (∃ out, out ∈ Turing.TM0.eval (Machine.mathProgram p) xs ∧ blockDecodedNumber out = some m) := by
  letI : Inhabited (Fin (states + 1)) := ⟨0⟩
  have hinit : Machine.mathConfig (⟨⟨0, by omega⟩, t⟩ : Machine.Config states) =
      Turing.TM0.init xs := by
    simp [Machine.mathConfig, Turing.TM0.init, ht]
  change (∃ d, Machine.Reaches p ⟨⟨0, by omega⟩, t⟩ d ∧ Machine.Halted p d ∧
      blockDecodedNumber (Machine.mathTape d.tape).right₀ = some m) ↔
    (∃ out, out ∈ (StateTransition.eval (Turing.TM0.step (Machine.mathProgram p))
      (Turing.TM0.init xs)).map (fun cfg => cfg.Tape.right₀) ∧ blockDecodedNumber out = some m)
  rw [← hinit, Machine.math_eval_configs]
  constructor
  · rintro ⟨d, hd, hh, ho⟩
    refine ⟨(Machine.mathTape d.tape).right₀, ?_, ho⟩
    apply (Part.mem_map_iff _).2
    refine ⟨Machine.mathConfig d, ?_, rfl⟩
    apply (Part.mem_map_iff _).2
    exact ⟨d, StateTransition.mem_eval.2 ⟨Machine.reaches_stateTransition.1 hd, hh⟩, rfl⟩
  · rintro ⟨out, hout, ho⟩
    obtain ⟨cfg, hcfg, he⟩ := (Part.mem_map_iff _).1 hout
    obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).1 hcfg
    obtain ⟨hr, hh⟩ := StateTransition.mem_eval.1 hd
    refine ⟨d, Machine.reaches_stateTransition.2 hr, hh, ?_⟩
    simpa [Machine.mathConfig, ← he] using ho

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryCompiled_block_result (c : Nat.Partrec.Code) (n m : Nat) :
    (∃ d, Machine.Reaches (unaryCompiledProgram c) (Machine.initial n) d ∧
      Machine.Halted (unaryCompiledProgram c) d ∧
      blockDecodedNumber (Machine.mathTape d.tape).right₀ = some m) ↔
        m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileRecoveredListCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  obtain ⟨mid, hpre, hhalt, htape⟩ := simulatorInputPreprocessor_correct n
  have hseq := Machine.sequence_observation_iff simulatorInputPreprocessor (blockProgram C)
    (Machine.initial n) mid hpre hhalt
    (fun t => blockDecodedNumber (Machine.mathTape t).right₀) m
  have hm := mathTape_block_observation_iff (blockProgram C) mid.tape
    (encodeSimSymbols (tm0ListInput [onesNumber n])) m htape
  change (∃ d, Machine.Reaches (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C))
      (Machine.initial n) d ∧ Machine.Halted (Machine.sequenceProgram simulatorInputPreprocessor (blockProgram C)) d ∧
      blockDecodedNumber (Machine.mathTape d.tape).right₀ = some m) ↔ _
  have hresult := hseq.trans (hm.trans (recoveredBlock_lambda_result c n m))
  simpa [Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hresult

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryCompiled_block_none (c : Nat.Partrec.Code) (n : Nat) :
    (¬ ∃ m d, Machine.Reaches (unaryCompiledProgram c) (Machine.initial n) d ∧
      Machine.Halted (unaryCompiledProgram c) d ∧
      blockDecodedNumber (Machine.mathTape d.tape).right₀ = some m) ↔
        numericalValue (compileLambdaTotal c) n = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro h m hm
    obtain ⟨d, hd, hh, ho⟩ := (unaryCompiled_block_result c n m).2 hm
    exact h ⟨m, d, hd, hh, ho⟩
  · rintro h ⟨m, d, hd, hh, ho⟩
    exact h m ((unaryCompiled_block_result c n m).1 ⟨d, hd, hh, ho⟩)

#print axioms unaryCompiled_block_result
#print axioms unaryCompiled_block_none
end LambdaTuring
