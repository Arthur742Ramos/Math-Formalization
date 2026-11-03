/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.InsertBlock
public meta import LambdaTuring.InsertBlock

@[expose] public section

namespace LambdaTuring.Machine

def consumeOne : Program 2 :=
  ⟨[none, some (⟨1, by decide⟩, .write .blank), none,
    some (⟨2, by decide⟩, .right)]⟩

def consumeStart (L : List Symbol) (n : Nat) : Config 2 :=
  ⟨⟨0, by decide⟩, ⟨L, .one, .one :: List.replicate n .one⟩⟩

def consumeEnd (L : List Symbol) (n : Nat) : Config 2 :=
  ⟨⟨2, by decide⟩, ⟨.blank :: L, .one, List.replicate n .one⟩⟩

theorem consumeOne_reaches (L : List Symbol) (n : Nat) :
    Reaches consumeOne (consumeStart L n) (consumeEnd L n) := by
  apply Reaches.step (b := ⟨⟨1, by decide⟩, ⟨L, .blank, .one :: List.replicate n .one⟩⟩)
  · rfl
  · exact .step rfl (.refl _)

theorem consumeOne_halts (L : List Symbol) (n : Nat) : Halted consumeOne (consumeEnd L n) := by rfl

theorem shiftTwelve_reaches (L : List Symbol) (n : Nat) :
    Reaches (shiftRepeat 12) (shiftPhaseConfig 12 ⟨0, by decide⟩ (shiftStart L n))
      (shiftPhaseConfig 12 ⟨11, by decide⟩ (shiftGap (List.replicate 11 .blank ++ L) n)) := by
  simpa using shiftRepeat_loop 12 ⟨0, by decide⟩ 11 (by decide) L n

theorem shiftTwelve_halts (L : List Symbol) (n : Nat) :
    Halted (shiftRepeat 12)
      (shiftPhaseConfig 12 ⟨11, by decide⟩ (shiftGap (List.replicate 11 .blank ++ L) n)) := by
  exact shiftRepeat_final_halts 12 ⟨11, by decide⟩ (by decide) _ _

/-- Replace the first of at least two unary cells with a fixed 13-cell block,
preserving the remaining unary cells and ending at their first symbol. -/
def consumeAndInsert (a : Symbol) (xs : List Symbol) :=
  sequenceProgram
    (sequenceProgram (sequenceProgram consumeOne (shiftRepeat 12)) (fixedMoveLeft 12))
    (fixedWriter (a :: xs))

theorem consumeAndInsert_runs (a : Symbol) (xs : List Symbol) (hxs : xs.length = 12)
    (L : List Symbol) (n : Nat) :
    let start := sequenceLeftConfig (n := 76) (m := 2 * (a :: xs).length)
      (sequenceLeftConfig (n := 63) (m := 12)
        (sequenceLeftConfig (n := 2) (m := 60) (consumeStart L n)))
    let finish := sequenceRightConfig (n := 76)
      (writerConfig (a :: xs) (a :: xs).length (by omega)
        ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩)
    Reaches (consumeAndInsert a xs) start finish ∧ Halted (consumeAndInsert a xs) finish := by
  let cStart := consumeStart L n
  let cEnd := consumeEnd L n
  let shStart := shiftPhaseConfig 12 ⟨0, by decide⟩ (shiftStart (.blank :: L) n)
  let shEnd := shiftPhaseConfig 12 ⟨11, by decide⟩
    (shiftGap (List.replicate 11 .blank ++ .blank :: L) n)
  have hshift : Reaches (shiftRepeat 12) ⟨⟨0, by decide⟩, cEnd.tape⟩ shEnd := by
    simpa [shStart, shEnd, shiftPhaseConfig, shiftPhaseState, shiftStart, cEnd, consumeEnd] using
      shiftTwelve_reaches (.blank :: L) n
  have h1 := sequence_complete consumeOne (shiftRepeat 12) cStart cEnd shEnd
    (consumeOne_reaches L n) (consumeOne_halts L n) hshift (shiftTwelve_halts (.blank :: L) n)
  let rewindTape : Tape := ⟨L, .blank, List.replicate 12 .blank ++ .one :: List.replicate n .one⟩
  let rewindEnd := leftMoveConfig 12 12 (by decide) rewindTape
  have hrewind : Reaches (fixedMoveLeft 12)
      ⟨⟨0, by decide⟩, shEnd.tape⟩ rewindEnd := by
    have h := fixedMoveLeft_reaches 12 0 (by decide) shEnd.tape
    have ht : ((moveLeft^[12]) shEnd.tape) = rewindTape := by
      simpa [shEnd, shiftPhaseConfig, rewindTape] using rewindShiftGap L n
    rw [ht] at h
    simpa [rewindEnd, leftMoveConfig, sequenceRightConfig] using h
  have h2 := sequence_complete (sequenceProgram consumeOne (shiftRepeat 12)) (fixedMoveLeft 12)
    (sequenceLeftConfig cStart) (sequenceRightConfig shEnd) rewindEnd
    h1.1 h1.2 hrewind (fixedMoveLeft_halts 12 rewindTape)
  have hw : writeRun (a :: xs) rewindTape =
      ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩ := by
    simpa [rewindTape, hxs] using writeRun_blank_cells a xs L (List.replicate n .one) .one
  let writeEnd := writerConfig (a :: xs) (a :: xs).length (by omega)
    ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩
  have hwriter : Reaches (fixedWriter (a :: xs)) ⟨⟨0, by omega⟩, rewindTape⟩ writeEnd := by
    have h := fixedWriter_run (a :: xs) rewindTape
    simpa [writerConfig, writeEnd, hw] using h
  exact sequence_complete
    (sequenceProgram (sequenceProgram consumeOne (shiftRepeat 12)) (fixedMoveLeft 12))
    (fixedWriter (a :: xs))
    (sequenceLeftConfig (n := 63) (m := 12) (sequenceLeftConfig (n := 2) (m := 60) cStart))
    (sequenceRightConfig (n := 63) rewindEnd) writeEnd h2.1 h2.2 hwriter (fixedWriter_halts (a :: xs) _)

#print axioms consumeAndInsert_runs
end LambdaTuring.Machine
