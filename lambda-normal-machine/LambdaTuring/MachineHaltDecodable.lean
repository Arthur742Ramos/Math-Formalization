/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.MachineHaltBridge
public meta import LambdaTuring.MachineHaltBridge
@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- Every halt of this compiler has a decodable unary output, not merely some
other terminal run with such an output. -/
theorem compiledUnaryMachine_halt_decodable (c : Code) (n : Nat)
    (d : Machine.Config _) (hr : Machine.Reaches (compiledUnaryMachine c) (Machine.initial n) d)
    (hh : Machine.Halted (compiledUnaryMachine c) d) :
    ∃ m, Machine.decode (d.tape.head :: d.tape.right) = some m := by
  obtain ⟨m, out, hout, houtHalt, hdecode⟩ :=
    (compiledUnaryMachine_halts_iff_yields c n).1 ⟨d, hr, hh⟩
  have heq := Machine.terminal_unique hr hout hh houtHalt
  subst out
  exact ⟨m, hdecode⟩

#print axioms compiledUnaryMachine_halt_decodable
end LambdaTuring
