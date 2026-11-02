/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputDispatch
public meta import LambdaTuring.OutputDispatch

@[expose] public section

namespace LambdaTuring.Machine

def outputReaderClass (q : Fin (mainReaderStateCount+1)) : Option Bool :=
  let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores q).2
  match decodeMainTriple s.1 s.2.1 s.2.2 with
  | some (some .bit1) => some true
  | some none => some false
  | _ => none

def outputValueLoop :=
  readLoopProgram mainReaderProgram safeMarkAppendNext clearThenSafeFinish outputReaderClass

/- One reader-driven bit-one pass, including its return to reader state.
The source head's value is checked before the source block is overwritten. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem outputValueLoop_one (t : Tape) (gap n : Nat)
    (old : Turing.ListBlank Symbol) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R))
    (hbit : (encodeSimAlphabet R.head).main = some .bit1) :
    ∃ u, Reaches outputValueLoop ⟨⟨0, by omega⟩, t⟩ ⟨⟨0, by omega⟩, u⟩ ∧
      mathTape u = Turing.Tape.mk' (safeScratch (13+gap) (n+1) old.tail)
        (encodeBlankSide R.tail) := by
  obtain ⟨rd, hrd, hrdh, hvalue, hrdtape⟩ := mainReader_table_runs t (safeScratch gap n old) R ht
  have hclass : outputReaderClass rd.state = some true := by
    unfold outputReaderClass
    dsimp only at hvalue ⊢
    rw [hvalue, hbit]
  have hmid : mathTape rd.tape = Turing.Tape.mk' (safeScratch gap n old) (encodeBlankSide R) :=
    hrdtape.trans ht
  obtain ⟨out, hout, houth, htape⟩ := safeMarkAppendNext_runs rd.tape gap n old R hmid
  have hread := readLoop_reader_reaches mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass _ _ hrd
  have hbranch := readLoop_reader_halt mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass rd hrdh true hclass
  have hbody := readLoop_body_reaches mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass _ _ hout
  have hback := readLoop_body_halt mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass out houth
  refine ⟨out.tape, ?_, htape⟩
  have hb := reaches_trans hbody (.step hback (.refl _))
  have hloop := reaches_trans hread (.step (by simpa using hbranch) hb)
  simpa [outputValueLoop, readLoopReaderConfig, readLoopReaderState] using hloop

/- A missing main-track value selects cleanup, which still scans the whole
source block and all remaining tracks before exposing the unary result. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem outputValueLoop_finish (t : Tape) (gap n offset : Nat)
    (old : Turing.ListBlank Symbol) (S : ∀ _ : StackIndex, List StackSymbol)
    (L : Turing.ListBlank (∀ _ : StackIndex, Option StackSymbol))
    (hproj : ∀ k, L.map (Turing.proj k) = Turing.ListBlank.mk ((S k).map some).reverse)
    (hoff : 0 < offset)
    (ht : mathTape t = Turing.Tape.mk' (safeScratch gap (n+1) old)
      (encodeBlankSide ((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L))))
    (hnone : (encodeSimAlphabet
      (((Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)).head)).main = none) :
    ∃ d, Reaches outputValueLoop ⟨⟨0, by omega⟩, t⟩ d ∧ Halted outputValueLoop d ∧
      decode (d.tape.head :: d.tape.right) = some n := by
  let R := (Turing.ListBlank.tail^[offset]) (Turing.TM2to1.addBottom L)
  obtain ⟨rd, hrd, hrdh, hvalue, hrdtape⟩ :=
    mainReader_table_runs t (safeScratch gap (n+1) old) R ht
  have hclass : outputReaderClass rd.state = some false := by
    unfold outputReaderClass
    dsimp only at hvalue ⊢
    rw [hvalue, hnone]
  have hmid : mathTape rd.tape = Turing.Tape.mk' (safeScratch gap (n+1) old) (encodeBlankSide R) :=
    hrdtape.trans ht
  obtain ⟨out, hout, houth, hdecode⟩ :=
    clearThenSafeFinish_observes rd.tape n offset gap old S L hproj hoff hmid
  have hread := readLoop_reader_reaches mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass _ _ hrd
  have hbranch := readLoop_reader_halt mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass rd hrdh false hclass
  have hfinal := readLoop_final_reaches mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass _ _ hout
  have hfinalhalt := readLoop_final_halt mainReaderProgram safeMarkAppendNext clearThenSafeFinish
    outputReaderClass out houth
  refine ⟨readLoopFinalConfig out, ?_, hfinalhalt, hdecode⟩
  have hloop := reaches_trans hread (.step (by simpa using hbranch) hfinal)
  simpa [outputValueLoop, readLoopReaderConfig, readLoopReaderState] using hloop

#print axioms outputValueLoop_one
#print axioms outputValueLoop_finish
end LambdaTuring.Machine
