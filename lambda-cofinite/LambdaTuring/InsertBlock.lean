/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryShiftRepeat
public meta import LambdaTuring.UnaryShiftRepeat
public import LambdaTuring.FixedMoveLeft
public meta import LambdaTuring.FixedMoveLeft
public import LambdaTuring.FixedBlockWriter
public meta import LambdaTuring.FixedBlockWriter
public import LambdaTuring.MachineSequence
public meta import LambdaTuring.MachineSequence

@[expose] public section

namespace LambdaTuring.Machine

/-- Shift a nonempty unary run thirteen cells right, rewind, and write a
fixed 13-cell block in the vacated space. -/
def insertBlock (a : Symbol) (xs : List Symbol) :=
  sequenceProgram (sequenceProgram (shiftRepeat 13) (fixedMoveLeft 12)) (fixedWriter (a :: xs))

theorem rewindShiftGap (L : List Symbol) (n : Nat) :
    ((moveLeft^[12]) (shiftGap (List.replicate 12 .blank ++ L) n).tape) =
      ⟨L, .blank, List.replicate 12 .blank ++ .one :: List.replicate n .one⟩ := by
  simp [shiftGap, Function.iterate_succ_apply, moveLeft, List.replicate_succ]

theorem insertBlock_runs (a : Symbol) (xs : List Symbol) (hxs : xs.length = 12)
    (L : List Symbol) (n : Nat) :
    let start := sequenceLeftConfig (sequenceLeftConfig
      (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart L n)))
    let finish := sequenceRightConfig
      (writerConfig (a :: xs) (a :: xs).length (by omega)
        ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩)
    Reaches (insertBlock a xs) start finish ∧ Halted (insertBlock a xs) finish := by
  let shiftStartCfg := shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart L n)
  let shiftEndCfg := shiftPhaseConfig 13 ⟨12, by decide⟩
    (shiftGap (List.replicate 12 .blank ++ L) n)
  let rewindTape : Tape := ⟨L, .blank, List.replicate 12 .blank ++ .one :: List.replicate n .one⟩
  let rewindEnd := leftMoveConfig 12 12 (by decide) rewindTape
  have hrewind : Reaches (fixedMoveLeft 12)
      ⟨⟨0, by decide⟩, shiftEndCfg.tape⟩ rewindEnd := by
    have h := fixedMoveLeft_reaches 12 0 (by decide) shiftEndCfg.tape
    have ht : ((moveLeft^[12]) shiftEndCfg.tape) = rewindTape := by
      simpa [shiftEndCfg, shiftPhaseConfig, rewindTape] using rewindShiftGap L n
    rw [ht] at h
    simpa [rewindEnd, leftMoveConfig] using h
  have hfirst := sequence_complete (shiftRepeat 13) (fixedMoveLeft 12)
    shiftStartCfg shiftEndCfg rewindEnd (shiftThirteen_reaches L n)
    (shiftThirteen_halts L n) hrewind (fixedMoveLeft_halts 12 rewindTape)
  have hw : writeRun (a :: xs) rewindTape =
      ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩ := by
    simpa [rewindTape, hxs] using writeRun_blank_cells a xs L (List.replicate n .one) .one
  let writeEnd := writerConfig (a :: xs) (a :: xs).length (by omega)
    ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩
  have hsecond : Reaches (fixedWriter (a :: xs))
      ⟨⟨0, by omega⟩, rewindTape⟩ writeEnd := by
    have h := fixedWriter_run (a :: xs) rewindTape
    simpa [writerConfig, writeEnd, hw] using h
  have hlast : Halted (fixedWriter (a :: xs)) writeEnd := by
    exact fixedWriter_halts (a :: xs) _
  exact sequence_complete (sequenceProgram (shiftRepeat 13) (fixedMoveLeft 12))
    (fixedWriter (a :: xs)) (sequenceLeftConfig shiftStartCfg) (sequenceRightConfig rewindEnd)
    writeEnd hfirst.1 hfirst.2 hsecond hlast

/-- Bounded execution is used only for the concrete check below. -/
def boundedHalt {states : Nat} (p : Program states) : Nat → Config states → Option (Config states)
  | 0, _ => none
  | fuel + 1, c => match step p c with
    | none => some c
    | some c' => boundedHalt p fuel c'

#eval (insertBlock .mark (List.replicate 12 .one)).table.length
#eval (boundedHalt (insertBlock .mark (List.replicate 12 .one)) 500
  (sequenceLeftConfig (sequenceLeftConfig (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart [] 2))))).map
    (fun c => c.tape)
#print axioms insertBlock_runs
end LambdaTuring.Machine
