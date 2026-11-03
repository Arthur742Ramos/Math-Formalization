/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ClearBlockLoop
public meta import LambdaTuring.ClearBlockLoop

@[expose] public section

namespace LambdaTuring

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem clearSweepProgram_of_run (t : Machine.Tape) (last : Turing.TM1.Cfg Machine.Symbol Unit Bool)
    (hr : StateTransition.Reaches (Turing.TM1.step clearSweep) ⟨some (), false, Machine.mathTape t⟩ last)
    (hh : Turing.TM1.step clearSweep last = none) :
    ∃ d, Machine.Reaches clearSweepProgram ⟨⟨0, by omega⟩, t⟩ d ∧
      Machine.Halted clearSweepProgram d ∧ Machine.mathTape d.tape = last.Tape := by
  let sourceStart : Turing.TM1.Cfg Machine.Symbol Unit Bool := ⟨some (), false, Machine.mathTape t⟩
  letI : Inhabited (TM1RawState Machine.Symbol Unit Bool) := ⟨tm1RawInitial clearSweep⟩
  letI : Inhabited (TM1NumberedState clearSweep [()] [false, true]) :=
    ⟨tm1NumberInitial clearSweep [()] [false, true]⟩
  have hsource : last ∈ StateTransition.eval (Turing.TM1.step clearSweep) sourceStart :=
    StateTransition.mem_eval.2 ⟨hr, hh⟩
  have hraw : Turing.TM1to0.trCfg clearSweep last ∈
      StateTransition.eval (Turing.TM0.step (tm1RawMachine clearSweep))
        (Turing.TM1to0.trCfg clearSweep sourceStart) := by
    change Turing.TM1to0.trCfg clearSweep last ∈
      StateTransition.eval (Turing.TM0.step (Turing.TM1to0.tr clearSweep))
        (Turing.TM1to0.trCfg clearSweep sourceStart)
    rw [StateTransition.tr_eval' _ _ _ (Turing.TM1to0.tr_respects clearSweep) sourceStart]
    exact (Part.mem_map_iff _).2 ⟨last, hsource, rfl⟩
  have hinit : (Turing.TM1to0.trCfg clearSweep sourceStart).q ∈
      Turing.TM1to0.trStmts clearSweep Finset.univ ∧
      Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw clearSweep [()] [false, true])
        (Turing.TM1to0.trCfg clearSweep sourceStart) =
      Turing.TM0.Cfg.mk (tm1NumberInitial clearSweep [()] [false, true]) (Machine.mathTape t) := by
    constructor
    · exact (tm1Raw_supports clearSweep).1
    · simp only [Turing.TM1to0.trCfg, sourceStart, Option.map_some, Turing.TM0.Cfg.map, genericTape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q (Machine.mathTape t))
        (tm1NumberRaw_initial clearSweep [()] [false, true])
  have hl : ∀ l : Unit, l ∈ [()] := by intro l; cases l; simp
  have hs : ∀ s : Bool, s ∈ [false, true] := by intro s; cases s <;> simp
  obtain ⟨num, ⟨_, hmap⟩, hnum⟩ := StateTransition.tr_eval
    (tm1NumberedMachine_respects clearSweep [()] [false, true] hl hs) hinit hraw
  have hnumTape : num.Tape = last.Tape := by
    rw [← hmap]
    simp [Turing.TM0.Cfg.map, Turing.TM1to0.trCfg, genericTape_id]
  let start : Machine.Config clearSweepStateCount := ⟨⟨0, by omega⟩, t⟩
  have hstart : Machine.mathConfig start =
      Turing.TM0.Cfg.mk (tm1NumberInitial clearSweep [()] [false, true]) (Machine.mathTape t) := by
    simp [start, Machine.mathConfig, tm1NumberInitial]
  have hprog : Machine.mathProgram clearSweepProgram = clearSweepTM0 := Machine.mathProgram_tableOfMathlib _
  have hnum' : num ∈ StateTransition.eval (Turing.TM0.step (Machine.mathProgram clearSweepProgram))
      (Machine.mathConfig start) := by
    rw [hprog, hstart]
    exact hnum
  rw [Machine.math_eval_configs] at hnum'
  obtain ⟨d, hd, heq⟩ := (Part.mem_map_iff _).1 hnum'
  obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.1 hd
  refine ⟨d, Machine.reaches_stateTransition.2 hreach, hhalt, ?_⟩
  have htape := congrArg Turing.TM0.Cfg.Tape heq
  simpa [Machine.mathConfig, hnumTape] using htape

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem clearSweepProgram_run (t : Machine.Tape) (T : Turing.Tape SimAlphabet)
    (ht : Machine.mathTape t = encodeBlockTape T)
    (hex : ∃ n, T.right₀.nth n = default) :
    ∃ n d, T.right₀.nth n = default ∧
      Machine.Reaches clearSweepProgram ⟨⟨0, by omega⟩, t⟩ d ∧
      Machine.Halted clearSweepProgram d ∧
      Machine.mathTape d.tape = (clearEnd ((clearNext^[n]) T)).Tape := by
  let n := Nat.find hex
  have hstop : T.right₀.nth n = default := Nat.find_spec hex
  have hprior : ∀ k, k < n → T.right₀.nth k ≠ default := fun k hk => Nat.find_min hex hk
  have hr := clearSweep_reaches T n hprior hstop
  have hh := clearSweep_end_halted ((clearNext^[n]) T)
  letI : Inhabited (TM1RawState Machine.Symbol Unit Bool) := ⟨tm1RawInitial clearSweep⟩
  letI : Inhabited (TM1NumberedState clearSweep [()] [false, true]) :=
    ⟨tm1NumberInitial clearSweep [()] [false, true]⟩
  have hsource : clearEnd ((clearNext^[n]) T) ∈
      StateTransition.eval (Turing.TM1.step clearSweep) (clearCfg T) :=
    StateTransition.mem_eval.2 ⟨hr, hh⟩
  have hraw : Turing.TM1to0.trCfg clearSweep (clearEnd ((clearNext^[n]) T)) ∈
      StateTransition.eval (Turing.TM0.step (tm1RawMachine clearSweep))
        (Turing.TM1to0.trCfg clearSweep (clearCfg T)) := by
    change Turing.TM1to0.trCfg clearSweep (clearEnd ((clearNext^[n]) T)) ∈
      StateTransition.eval (Turing.TM0.step (Turing.TM1to0.tr clearSweep))
        (Turing.TM1to0.trCfg clearSweep (clearCfg T))
    rw [StateTransition.tr_eval' _ _ _ (Turing.TM1to0.tr_respects clearSweep) (clearCfg T)]
    exact (Part.mem_map_iff _).2 ⟨_, hsource, rfl⟩
  have hinit : (Turing.TM1to0.trCfg clearSweep (clearCfg T)).q ∈
      Turing.TM1to0.trStmts clearSweep Finset.univ ∧
      Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw clearSweep [()] [false, true])
        (Turing.TM1to0.trCfg clearSweep (clearCfg T)) =
      Turing.TM0.Cfg.mk (tm1NumberInitial clearSweep [()] [false, true]) (encodeBlockTape T) := by
    constructor
    · exact (tm1Raw_supports clearSweep).1
    · simp only [Turing.TM1to0.trCfg, clearCfg, Option.map_some, Turing.TM0.Cfg.map, genericTape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q (encodeBlockTape T))
        (tm1NumberRaw_initial clearSweep [()] [false, true])
  have hl : ∀ l : Unit, l ∈ [()] := by intro l; cases l; simp
  have hs : ∀ s : Bool, s ∈ [false, true] := by intro s; cases s <;> simp
  obtain ⟨num, ⟨_, hmap⟩, hnum⟩ := StateTransition.tr_eval
    (tm1NumberedMachine_respects clearSweep [()] [false, true] hl hs) hinit hraw
  have hnumTape : num.Tape = (clearEnd ((clearNext^[n]) T)).Tape := by
    rw [← hmap]
    simp [Turing.TM0.Cfg.map, Turing.TM1to0.trCfg, genericTape_id]
  let start : Machine.Config clearSweepStateCount := ⟨⟨0, by omega⟩, t⟩
  have hstart : Machine.mathConfig start =
      Turing.TM0.Cfg.mk (tm1NumberInitial clearSweep [()] [false, true]) (encodeBlockTape T) := by
    simp [start, Machine.mathConfig, ht, tm1NumberInitial]
  have hprog : Machine.mathProgram clearSweepProgram = clearSweepTM0 := Machine.mathProgram_tableOfMathlib _
  have hnum' : num ∈ StateTransition.eval (Turing.TM0.step (Machine.mathProgram clearSweepProgram))
      (Machine.mathConfig start) := by
    rw [hprog, hstart]
    exact hnum
  rw [Machine.math_eval_configs] at hnum'
  obtain ⟨d, hd, heq⟩ := (Part.mem_map_iff _).1 hnum'
  obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.1 hd
  refine ⟨n, d, hstop, Machine.reaches_stateTransition.2 hreach, hhalt, ?_⟩
  have htape := congrArg Turing.TM0.Cfg.Tape heq
  simpa [Machine.mathConfig, hnumTape] using htape

#print axioms clearSweepProgram_run
#print axioms clearSweepProgram_of_run
end LambdaTuring
