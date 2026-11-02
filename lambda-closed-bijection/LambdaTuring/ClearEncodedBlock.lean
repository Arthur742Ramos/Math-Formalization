/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryOutputShapeBridge
public meta import LambdaTuring.UnaryOutputShapeBridge
public import LambdaTuring.FixedBlockWriter
public meta import LambdaTuring.FixedBlockWriter

@[expose] public section

namespace LambdaTuring

theorem mathTape_writeRun (xs : List Machine.Symbol) (t : Machine.Tape) :
    Machine.mathTape (Machine.writeRun xs t) = writeBlock xs (Machine.mathTape t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih =>
    simp only [Machine.writeRun, writeBlock]
    rw [ih, Machine.mathTape_moveRight]
    have h := Machine.mathTape_perform (.write a) t
    change Machine.mathTape { t with head := a } = (Machine.mathTape t).write a at h
    rw [h]

theorem writeBlock_encoded_blank (T : Turing.Tape SimAlphabet) :
    writeBlock (List.replicate 13 .blank) (encodeBlockTape T) =
      ((Turing.Tape.move .right)^[13]) (encodeBlockTape (T.write default)) := by
  have h := encodeBlockTape_write T default
  rw [encodeSimSymbol_blank] at h
  have hinv : Function.LeftInverse (Turing.Tape.move .right : Turing.Tape Machine.Symbol → _)
      (Turing.Tape.move .left) := Turing.Tape.move_left_right
  have h' := congrArg ((Turing.Tape.move .right)^[13]) h
  rw [(hinv.iterate 13) _] at h'
  exact h'.symm

/-- The finite fixed-block writer erases one encoded source cell and ends at
the next source-cell boundary, without changing the rest of the tape. -/
theorem clearEncodedBlock (t : Machine.Tape) (T : Turing.Tape SimAlphabet)
    (ht : Machine.mathTape t = encodeBlockTape T) :
    ∃ d, Machine.Reaches (Machine.fixedWriter (List.replicate 13 .blank))
      ⟨⟨0, by decide⟩, t⟩ d ∧
      Machine.Halted (Machine.fixedWriter (List.replicate 13 .blank)) d ∧
      Machine.mathTape d.tape =
        ((Turing.Tape.move .right)^[13]) (encodeBlockTape (T.write default)) := by
  let xs := List.replicate 13 Machine.Symbol.blank
  let d := Machine.writerConfig xs xs.length (by omega) (Machine.writeRun xs t)
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa [d, xs, Machine.writerConfig] using Machine.fixedWriter_run xs t
  · exact Machine.fixedWriter_halts xs _
  · change Machine.mathTape (Machine.writeRun xs t) = _
    rw [mathTape_writeRun, ht]
    exact writeBlock_encoded_blank T

#print axioms clearEncodedBlock
end LambdaTuring
