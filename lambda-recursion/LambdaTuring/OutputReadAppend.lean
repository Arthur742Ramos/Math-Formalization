/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ReaderFiniteControl
public meta import LambdaTuring.ReaderFiniteControl
public import LambdaTuring.OutputAppendBridge
public meta import LambdaTuring.OutputAppendBridge

@[expose] public section

namespace LambdaTuring.Machine

/- This fixed sequence reads a block and then appends one cell regardless of
the value read. It is the bit-one branch, not yet the reader-driven loop. -/
def readThenAppend := sequenceProgram mainReaderProgram markAppendNext

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem readThenAppend_runs (t : Tape) (gap n : Nat) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (encodeBlankSide R)) :
    ∃ rd out, Reaches mainReaderProgram ⟨⟨0, by omega⟩, t⟩ rd ∧
      Halted mainReaderProgram rd ∧
      (let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores rd.state).2
       decodeMainTriple s.1 s.2.1 s.2.2 = some (encodeSimAlphabet R.head).main) ∧
      Reaches readThenAppend ⟨⟨0, by omega⟩, t⟩ out ∧ Halted readThenAppend out ∧
      mathTape out.tape = Turing.Tape.mk'
        (Turing.ListBlank.mk (List.replicate (13+gap) .blank ++ .mark :: List.replicate (n+1) .one))
        (encodeBlankSide R.tail) := by
  obtain ⟨rd, hrd, hrdh, hvalue, hrdtape⟩ := mainReader_table_runs t
    (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one)) R ht
  have hmid : mathTape rd.tape = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (encodeBlankSide R) := hrdtape.trans ht
  obtain ⟨out, hout, houth, houttape⟩ := markAppendNext_runs rd.tape gap n R hmid
  have hs := sequence_complete mainReaderProgram markAppendNext ⟨⟨0, by omega⟩, t⟩ rd out
    hrd hrdh hout houth
  refine ⟨rd, sequenceRightConfig out, hrd, hrdh, hvalue, ?_, hs.2, ?_⟩
  · simpa [readThenAppend, sequenceLeftConfig, sequenceLeftState] using hs.1
  · exact houttape

#print axioms readThenAppend_runs
end LambdaTuring.Machine
