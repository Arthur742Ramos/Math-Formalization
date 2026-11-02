/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputInitialize
public meta import LambdaTuring.OutputInitialize

@[expose] public section

namespace LambdaTuring

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOutput_joint (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    let C := compileUnaryOutputCode c
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    ∃ (out : Turing.ListBlank SimAlphabet) (S : ∀ _ : StackIndex, List StackSymbol)
      (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)),
      out ∈ Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n]) ∧
      Turing.TM2to1.addBottom L = out ∧
      (∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse) ∧
      L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
        Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
          List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)) := by
  let C := compileUnaryOutputCode c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  rw [(compileLambdaTotal_sound c).2 n] at hm
  have hc : [onesNumber m] ∈ C.eval [onesNumber n] := by
    rw [compileUnaryOutputCode_eval]
    exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
  have hd : (Turing.TM0.eval (tm0ListInterpreter C) (tm0ListInput [onesNumber n])).Dom :=
    (tm0List_domain C [onesNumber n]).2 (Part.dom_iff_mem.2 ⟨[onesNumber m], hc⟩)
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.1 hd
  obtain ⟨S, L, heq, hproj, hmain⟩ :=
    tm0List_output_relation C [onesNumber n] [onesNumber m] out hout hc
  refine ⟨out, S, L, hout, heq, hproj, ?_⟩
  have hp := hproj Turing.PartrecToTM2.K'.main
  rw [hmain, trList_ones] at hp
  simpa [List.map_append, List.map_replicate, List.reverse_append] using hp

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem unaryOnesProgram_joint (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    let C := compileUnaryOutputCode c
    let preSize := Machine.prefixLoopSize .mark .one prefixTail bitTail + 2 + 1
    ∃ (d : Machine.Config (BlockTM0StateCount C)) (S : ∀ _ : StackIndex, List StackSymbol)
      (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol)),
      Machine.Reaches (unaryOnesProgram c) (Machine.initial n) (Machine.sequenceRightConfig (n := preSize) d) ∧
      Machine.Halted (unaryOnesProgram c) (Machine.sequenceRightConfig (n := preSize) d) ∧
      (Machine.mathTape d.tape).right₀ = encodeBlankSide (Turing.TM2to1.addBottom L) ∧
      (∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse) ∧
      L.map (Turing.proj Turing.PartrecToTM2.K'.main) =
        Turing.ListBlank.mk (some Turing.PartrecToTM2.Γ'.cons ::
          List.replicate (m+1) (some Turing.PartrecToTM2.Γ'.bit1)) := by
  let C := compileUnaryOutputCode c
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  obtain ⟨out, S, L, hout, heq, hproj, hshape⟩ := unaryOutput_joint c n m hm
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
  refine ⟨d, S, L, ?_, hseq.2, ?_, hproj, hshape⟩
  · simpa [unaryOnesProgram, C, Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hseq.1
  · exact hdo.trans (congrArg encodeBlankSide heq.symm)

def compiledUnaryMachine (c : Nat.Partrec.Code) :=
  Machine.sequenceProgram (unaryOnesProgram c) Machine.unaryOutputConverter

theorem Machine.sequence_yields_of_run {aSize bSize : Nat} (a : Machine.Program aSize)
    (b : Machine.Program bSize) (n m : Nat) (mid : Machine.Config aSize) (out : Machine.Config bSize)
    (hr : Machine.Reaches a (Machine.initial n) mid) (hh : Machine.Halted a mid)
    (hr₂ : Machine.Reaches b ⟨⟨0, by omega⟩, mid.tape⟩ out) (hh₂ : Machine.Halted b out)
    (hdec : Machine.decode (out.tape.head :: out.tape.right) = some m) :
    Machine.Yields (Machine.sequenceProgram a b) n m := by
  have hs := Machine.sequence_complete a b (Machine.initial n) mid out hr hh hr₂ hh₂
  refine ⟨Machine.sequenceRightConfig out, ?_, hs.2, hdec⟩
  simpa [Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hs.1

def Machine.ResultRun {k : Nat} (b : Machine.Program k) (t : Machine.Tape) (m : Nat) : Prop :=
  ∃ d, Machine.Reaches b ⟨⟨0, Nat.zero_lt_succ _⟩, t⟩ d ∧ Machine.Halted b d ∧
    Machine.decode (d.tape.head :: d.tape.right) = some m

theorem Machine.sequence_yields_of_result {aSize bSize : Nat} (a : Machine.Program aSize)
    (b : Machine.Program bSize) (n m : Nat) (mid : Machine.Config aSize)
    (hr : Machine.Reaches a (Machine.initial n) mid) (hh : Machine.Halted a mid)
    (hc : Machine.ResultRun b mid.tape m) :
    Machine.Yields (Machine.sequenceProgram a b) n m := by
  obtain ⟨out, hout, houth, hdec⟩ := hc
  exact Machine.sequence_yields_of_run a b n m mid out hr hh hout houth hdec

theorem Machine.sequenceRight_tape {n m : Nat} (d : Machine.Config m) :
    (Machine.sequenceRightConfig (n := n) d).tape = d.tape := rfl

theorem Machine.sequence_yields_of_result_on_tape {aSize bSize : Nat} (a : Machine.Program aSize)
    (b : Machine.Program bSize) (n m : Nat) (mid : Machine.Config aSize) (t : Machine.Tape)
    (hr : Machine.Reaches a (Machine.initial n) mid) (hh : Machine.Halted a mid)
    (ht : mid.tape = t) (hc : Machine.ResultRun b t m) :
    Machine.Yields (Machine.sequenceProgram a b) n m := by
  apply Machine.sequence_yields_of_result a b n m mid hr hh
  rw [ht]
  exact hc

/- A sequence can only halt after its first component has halted. This does
not assume that the second component returns a numerical observation. -/
theorem Machine.sequence_first_halts {aSize bSize : Nat} (a : Machine.Program aSize)
    (b : Machine.Program bSize) (start : Machine.Config aSize)
    (z : Machine.Config (aSize+bSize+1))
    (hr : Machine.Reaches (Machine.sequenceProgram a b) (Machine.sequenceLeftConfig start) z)
    (hh : Machine.Halted (Machine.sequenceProgram a b) z) :
    ∃ mid, Machine.Reaches a start mid ∧ Machine.Halted a mid := by
  have aux : ∀ x y, Machine.Reaches (Machine.sequenceProgram a b) x y →
      ∀ c : Machine.Config aSize, x = Machine.sequenceLeftConfig c →
        Machine.Halted (Machine.sequenceProgram a b) y →
        ∃ mid, Machine.Reaches a c mid ∧ Machine.Halted a mid := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro c hc hhalt
      rw [hc] at hhalt
      cases ha : Machine.step a c with
      | none => exact ⟨c, .refl _, ha⟩
      | some d =>
        have hs := Machine.sequence_left_step a b c d ha
        change Machine.step (Machine.sequenceProgram a b) (Machine.sequenceLeftConfig c) = none at hhalt
        rw [hhalt] at hs
        cases hs
    | @step x next y hs _ ih =>
      intro c hc hhalt
      subst x
      cases ha : Machine.step a c with
      | none => exact ⟨c, .refl _, ha⟩
      | some d =>
        have hs' := Machine.sequence_left_step a b c d ha
        have he : next = Machine.sequenceLeftConfig d := Option.some.inj (hs.symm.trans hs')
        subst next
        obtain ⟨mid, hm, hmh⟩ := ih d rfl hhalt
        exact ⟨mid, .step ha hm, hmh⟩
  exact aux _ _ hr start rfl hh

theorem Machine.sequence_yields_first_halts {aSize bSize : Nat}
    (a : Machine.Program aSize) (b : Machine.Program bSize) (n m : Nat)
    (hy : Machine.Yields (Machine.sequenceProgram a b) n m) :
    ∃ mid, Machine.Reaches a (Machine.initial n) mid ∧ Machine.Halted a mid := by
  obtain ⟨z, hr, hh, _⟩ := hy
  apply Machine.sequence_first_halts a b (Machine.initial n) z ?_ hh
  simpa [Machine.sequenceLeftConfig, Machine.sequenceLeftState, Machine.initial] using hr

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem compiledUnaryMachine_yields (c : Nat.Partrec.Code) (n m : Nat)
    (hm : m ∈ numericalValue (compileLambdaTotal c) n) :
    Machine.Yields (compiledUnaryMachine c) n m := by
  obtain ⟨mid, S, L, hrun, hhalt, htape, hproj, hshape⟩ := unaryOnesProgram_joint c n m hm
  obtain ⟨out, hout, houth, hdecoded⟩ :=
    Machine.unaryOutputConverter_observes mid.tape m S L hproj hshape htape
  let mid' := Machine.sequenceRightConfig
    (n := Machine.prefixLoopSize .mark .one prefixTail bitTail + 2 + 1) mid
  have hrun' : Machine.Reaches (unaryOnesProgram c) (Machine.initial n) mid' := hrun
  have hhalt' : Machine.Halted (unaryOnesProgram c) mid' := hhalt
  have hmidTape := Machine.sequenceRight_tape
    (n := Machine.prefixLoopSize .mark .one prefixTail bitTail + 2 + 1) mid
  have hc : Machine.ResultRun Machine.unaryOutputConverter mid.tape m := ⟨out, hout, houth, hdecoded⟩
  exact Machine.sequence_yields_of_result_on_tape (unaryOnesProgram c) Machine.unaryOutputConverter n m
    mid' mid.tape hrun' hhalt' hmidTape hc

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem compiledUnaryMachine_yields_iff (c : Nat.Partrec.Code) (n m : Nat) :
    Machine.Yields (compiledUnaryMachine c) n m ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  constructor
  · intro hy
    obtain ⟨mid, hrun, hhalt⟩ := Machine.sequence_yields_first_halts
      (unaryOnesProgram c) Machine.unaryOutputConverter n m hy
    have hdom := (unaryOnesProgram_terminates_iff c n).1 ⟨mid, hrun, hhalt⟩
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 hdom
    have hyk := compiledUnaryMachine_yields c n k hk
    have heq : m = k := Machine.yields_unique hy hyk
    simpa [heq] using hk
  · exact compiledUnaryMachine_yields c n m

theorem compiledUnaryMachine_no_numerical_result (c : Nat.Partrec.Code) (n : Nat) :
    (¬ ∃ m, Machine.Yields (compiledUnaryMachine c) n m) ↔
      numericalValue (compileLambdaTotal c) n = Part.none := by
  constructor
  · intro h
    apply Part.eq_none_iff.2
    intro m hm
    exact h ⟨m, (compiledUnaryMachine_yields_iff c n m).2 hm⟩
  · intro h ⟨m, hm⟩
    exact (Part.eq_none_iff.1 h) m ((compiledUnaryMachine_yields_iff c n m).1 hm)

#print axioms unaryOnesProgram_joint
#print axioms compiledUnaryMachine_yields
#print axioms compiledUnaryMachine_yields_iff
#print axioms compiledUnaryMachine_no_numerical_result
#print axioms compiledUnaryMachine
end LambdaTuring
