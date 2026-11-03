/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.OutputEndToEnd
public meta import LambdaTuring.OutputEndToEnd
@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- The compiled machine can halt only after its first component halts;
for this compiler every such halt produces a numerical observation. -/
theorem compiledUnaryMachine_halts_iff_yields (c : Code) (n : Nat) :
    (∃ d, Machine.Reaches (compiledUnaryMachine c) (Machine.initial n) d ∧
      Machine.Halted (compiledUnaryMachine c) d) ↔
      ∃ m, Machine.Yields (compiledUnaryMachine c) n m := by
  constructor
  · rintro ⟨d, hd, hhalt⟩
    obtain ⟨mid, hrun, hmid⟩ := Machine.sequence_first_halts
      (unaryOnesProgram c) Machine.unaryOutputConverter (Machine.initial n) d
      (by simpa [compiledUnaryMachine, Machine.sequenceLeftConfig,
        Machine.sequenceLeftState, Machine.initial] using hd) hhalt
    have hdom := (unaryOnesProgram_terminates_iff c n).1 ⟨mid, hrun, hmid⟩
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 hdom
    exact ⟨m, compiledUnaryMachine_yields c n m hm⟩
  · rintro ⟨m, d, hd, hh, _⟩
    exact ⟨d, hd, hh⟩

#print axioms compiledUnaryMachine_halts_iff_yields
end LambdaTuring
