/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputQuotient
public meta import LambdaTuring.OutputQuotient
public import LambdaTuring.ClearEncodedBlock
public meta import LambdaTuring.ClearEncodedBlock
public import LambdaTuring.FixedMoveLeft
public meta import LambdaTuring.FixedMoveLeft

@[expose] public section

namespace LambdaTuring

def waypointBlock : List Machine.Symbol := .mark :: List.replicate 12 .blank

theorem waypointBlock_length : waypointBlock.length = 13 := by rfl

def markOutputBlock :=
  Machine.sequenceProgram (Machine.fixedWriter waypointBlock) (Machine.fixedMoveLeft 13)

theorem mathTape_moveLeft_iter (n : Nat) (t : Machine.Tape) :
    Machine.mathTape ((Machine.moveLeft^[n]) t) =
      ((Turing.Tape.move .left)^[n]) (Machine.mathTape t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [ih, Machine.mathTape_moveLeft]

/- The reader must consume the main-track data before this operation. It
replaces exactly one source cell with a marker and twelve blanks, preserving
the arbitrary left scratch and the entire unprocessed encoded tail. -/
theorem markOutputBlock_runs (t : Machine.Tape) (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet)
    (ht : Machine.mathTape t = Turing.Tape.mk' L (encodeBlankSide R)) :
    ∃ d, Machine.Reaches markOutputBlock (Machine.sequenceLeftConfig
        (Machine.writerConfig waypointBlock 0 (by omega) t)) d ∧
      Machine.Halted markOutputBlock d ∧
      Machine.mathTape d.tape =
        Turing.Tape.mk' L (Turing.ListBlank.append waypointBlock (encodeBlankSide R.tail)) := by
  let d₁ := Machine.writerConfig waypointBlock waypointBlock.length (by omega)
    (Machine.writeRun waypointBlock t)
  let d₂ := Machine.leftMoveConfig 13 13 (by omega)
    ((Machine.moveLeft^[13]) (Machine.writeRun waypointBlock t))
  have hw : Machine.Reaches (Machine.fixedWriter waypointBlock)
      (Machine.writerConfig waypointBlock 0 (by omega) t) d₁ :=
    Machine.fixedWriter_run waypointBlock t
  have hh := Machine.fixedWriter_halts waypointBlock (Machine.writeRun waypointBlock t)
  have hm : Machine.Reaches (Machine.fixedMoveLeft 13) ⟨⟨0, by omega⟩, d₁.tape⟩ d₂ := by
    simpa [d₁, d₂, Machine.writerConfig, Machine.leftMoveConfig] using
      Machine.fixedMoveLeft_reaches 13 0 (by omega) (Machine.writeRun waypointBlock t)
  have hs := Machine.sequence_complete (Machine.fixedWriter waypointBlock) (Machine.fixedMoveLeft 13)
    (Machine.writerConfig waypointBlock 0 (by omega) t) d₁ d₂ hw hh hm
    (Machine.fixedMoveLeft_halts 13 _)
  refine ⟨Machine.sequenceRightConfig d₂, hs.1, hs.2, ?_⟩
  change Machine.mathTape ((Machine.moveLeft^[13]) (Machine.writeRun waypointBlock t)) = _
  rw [mathTape_moveLeft_iter, mathTape_writeRun, ht]
  have hR : encodeBlankSide R =
      Turing.ListBlank.append (encodeSimSymbol R.head) (encodeBlankSide R.tail) := by
    conv_lhs => rw [← Turing.ListBlank.cons_head_tail R]
    exact encodeBlankSide_cons R.head R.tail
  rw [hR]
  have hlen : waypointBlock.length = (encodeSimSymbol R.head).length := by
    simpa [waypointBlock_length, encodeSimSymbol] using
      (encodeSymbolBlock_length (encodeSimAlphabet R.head)).symm
  rw [writeBlock_list waypointBlock (encodeSimSymbol R.head) L (encodeBlankSide R.tail) hlen]
  have hmove := tape_move_right_list waypointBlock L (encodeBlankSide R.tail)
  rw [waypointBlock_length] at hmove
  rw [← hmove]
  have hinv : Function.LeftInverse (Turing.Tape.move .left : Turing.Tape Machine.Symbol → _)
      (Turing.Tape.move .right) := Turing.Tape.move_right_left
  exact hinv.iterate 13 _

#print axioms markOutputBlock_runs
end LambdaTuring
