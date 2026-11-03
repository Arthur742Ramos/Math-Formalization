/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MainTrackMachine
public meta import LambdaTuring.MainTrackMachine

@[expose] public section

namespace LambdaTuring.Machine

/- Unlike a general simulation, this bridge takes exactly one concrete
table step for each Mathlib TM0 step, even when tape lists differ by blanks. -/
theorem mathReachLift {states : Nat} (p : Program states) (c : Config states)
    (q : Turing.TM0.Cfg Symbol (Fin (states+1)))
    (h : StateTransition.Reaches (Turing.TM0.step (mathProgram p)) (mathConfig c) q) :
    ∃ d, Reaches p c d ∧ mathConfig d = q := by
  have aux : ∀ x y, StateTransition.Reaches (Turing.TM0.step (mathProgram p)) x y →
      ∀ a, mathConfig a = x → ∃ b, Reaches p a b ∧ mathConfig b = y := by
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro a ha
      exact ⟨a, .refl _, ha⟩
    | head hs _ ih =>
      intro a ha
      rw [← ha, ← math_step p a] at hs
      cases hstep : step p a with
      | none => simp [hstep] at hs
      | some b =>
        simp only [hstep, Option.map_some, Option.mem_def, Option.some.injEq] at hs
        obtain ⟨d, hd, heq⟩ := ih b hs
        exact ⟨d, .step hstep hd, heq⟩
  exact aux _ _ h c rfl

theorem mathHaltLift {states : Nat} (p : Program states) (c : Config states)
    (h : Turing.TM0.step (mathProgram p) (mathConfig c) = none) : Halted p c := by
  have hs := math_step p c
  rw [h] at hs
  cases hstep : step p c with
  | none => exact hstep
  | some d => simp [hstep] at hs

end LambdaTuring.Machine

namespace LambdaTuring

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem mainReader_table_runs (t : Machine.Tape) (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) (ht : Machine.mathTape t = Turing.Tape.mk' L (encodeBlankSide R)) :
    ∃ d, Machine.Reaches mainReaderProgram ⟨⟨0, by omega⟩, t⟩ d ∧ Machine.Halted mainReaderProgram d ∧
      (let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores d.state).2
       decodeMainTriple s.1 s.2.1 s.2.2 = some (encodeSimAlphabet R.head).main) ∧
      Machine.mathTape d.tape = Machine.mathTape t := by
  letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
  letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
    ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
  obtain ⟨q, hq, hdecode, htape, hhalt⟩ := mainReader_numbered_reads_halted L R
  let start : Machine.Config mainReaderStateCount := ⟨⟨0, by omega⟩, t⟩
  have hstart : Machine.mathConfig start =
      Turing.TM0.Cfg.mk (tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores)
        (Turing.Tape.mk' L (encodeBlankSide R)) := by
    simp [start, Machine.mathConfig, tm1NumberInitial, ht]
  have hp : Machine.mathProgram mainReaderProgram = mainReaderTM0 := Machine.mathProgram_tableOfMathlib _
  have hq' : StateTransition.Reaches (Turing.TM0.step (Machine.mathProgram mainReaderProgram))
      (Machine.mathConfig start) q := by rw [hp, hstart]; exact hq
  obtain ⟨d, hd, heq⟩ := Machine.mathReachLift mainReaderProgram start q hq'
  have hdh : Machine.Halted mainReaderProgram d := by
    apply Machine.mathHaltLift
    rw [hp, heq]
    exact hhalt
  have hstate : d.state = q.q := by
    have h := congrArg Turing.TM0.Cfg.q heq
    simpa [Machine.mathConfig] using h
  have hdtape : Machine.mathTape d.tape = Machine.mathTape t := by
    have h := congrArg Turing.TM0.Cfg.Tape heq
    simpa [Machine.mathConfig, htape, ht] using h
  refine ⟨d, hd, hdh, ?_, hdtape⟩
  rw [hstate]
  exact hdecode

#print axioms Machine.mathReachLift
#print axioms mainReader_table_runs
end LambdaTuring
