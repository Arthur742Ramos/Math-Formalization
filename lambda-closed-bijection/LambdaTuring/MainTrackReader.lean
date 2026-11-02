/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ClearBlockSide
public meta import LambdaTuring.ClearBlockSide

@[expose] public section

namespace LambdaTuring

abbrev MainStore := Machine.Symbol × Machine.Symbol × Machine.Symbol
inductive MainLabel where
  | start
  | done (value : Option StackState)
  deriving DecidableEq

instance : Inhabited MainLabel := ⟨.start⟩
abbrev MainStmt := Turing.TM1.Stmt Machine.Symbol MainLabel MainStore

def decodeMainTriple (a b c : Machine.Symbol) : Option StackState :=
  if [a,b,c] = List.replicate 3 .blank then some none
  else (decodeTrack [a,b,c]).map Prod.fst

def mainTrackReader : MainLabel → MainStmt
  | .start =>
    .move .right (.load (fun a s => (a, s.2.1, s.2.2))
      (.move .right (.load (fun b s => (s.1, b, s.2.2))
      (.move .right (.load (fun c s => (s.1, s.2.1, c))
      (.move .left (.move .left (.move .left
        (.goto fun _ s => .done (decodeMainTriple s.1 s.2.1 s.2.2))))))))))
  | .done _ => .halt

def mainTrackTriple (t : Turing.Tape Machine.Symbol) : MainStore :=
  ((t.move .right).head, ((Turing.Tape.move .right)^[2] t).head,
    ((Turing.Tape.move .right)^[3] t).head)

theorem mainTrackReader_step (t : Turing.Tape Machine.Symbol) (store : MainStore) :
    Turing.TM1.stepAux (mainTrackReader .start) store t =
      ⟨some (.done (decodeMainTriple (mainTrackTriple t).1
        (mainTrackTriple t).2.1 (mainTrackTriple t).2.2)), mainTrackTriple t, t⟩ := by
  simp [mainTrackReader, Turing.TM1.stepAux, mainTrackTriple, Function.iterate_succ_apply,
    Turing.Tape.move_right_left]

def mainTrackSegment (t : Turing.Tape Machine.Symbol) : List Machine.Symbol :=
  [(mainTrackTriple t).1, (mainTrackTriple t).2.1, (mainTrackTriple t).2.2]

theorem mainTrackSegment_readBlock (t : Turing.Tape Machine.Symbol) :
    mainTrackSegment t = ((readBlock t).drop 1).take 3 := by
  simp only [mainTrackSegment, mainTrackTriple, readBlock, List.ofFn_succ,
    Turing.Tape.move_right_n_head]
  simpa [Function.iterate_succ_apply] using (Turing.Tape.move_right_n_head t 1)

theorem readBlock_same_right (t u : Turing.Tape Machine.Symbol) (h : t.right₀ = u.right₀) :
    readBlock t = readBlock u := by
  apply List.ext_getElem
  · simp [readBlock]
  · intro i hi hj
    simp only [readBlock, List.getElem_ofFn, Turing.Tape.move_right_n_head,
      ← Turing.Tape.right₀_nth, h]

theorem readBlock_side (L : Turing.ListBlank Machine.Symbol) (R : Turing.ListBlank SimAlphabet) :
    readBlock (Turing.Tape.mk' L (encodeBlankSide R)) = encodeSimSymbol R.head := by
  have he : (Turing.Tape.mk' L (encodeBlankSide R)).right₀ =
      (encodeBlockTape (Turing.Tape.mk' ∅ R)).right₀ := by
    simp [encodeBlockTape]
  rw [readBlock_same_right _ _ he, readBlock_encodeBlockTape]
  rfl

def decodeMainList : List Machine.Symbol → Option StackState
  | [a,b,c] => decodeMainTriple a b c
  | _ => none

theorem decodeMainList_track (s : StackState) : decodeMainList (encodeTrack s) = some s := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

theorem decodeMainList_block (a : SimAlphabetData) :
    decodeMainList (((encodeSymbolBlock a).drop 1).take 3) = some a.main := by
  by_cases h : a = blankSimAlphabetData
  · subst a
    rfl
  · simp only [encodeSymbolBlock, h, ↓reduceIte, encodeSymbolBody]
    change decodeMainList ((encodeTrack a.main ++ encodeTrack a.rev ++
      encodeTrack a.aux ++ encodeTrack a.stack).take 3) = some a.main
    have hlen := encodeTrack_length a.main
    simp only [List.append_assoc]
    rw [List.take_append_of_le_length (by omega), ← hlen]
    simpa using decodeMainList_track a.main

theorem mainTrackReader_decodes (L : Turing.ListBlank Machine.Symbol) (R : Turing.ListBlank SimAlphabet) :
    decodeMainList (mainTrackSegment (Turing.Tape.mk' L (encodeBlankSide R))) =
      some (encodeSimAlphabet R.head).main := by
  rw [mainTrackSegment_readBlock, readBlock_side]
  exact decodeMainList_block (encodeSimAlphabet R.head)

theorem mainTrackReader_side_step (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) (store : MainStore) :
    Turing.TM1.stepAux (mainTrackReader .start) store
        (Turing.Tape.mk' L (encodeBlankSide R)) =
      ⟨some (.done (some (encodeSimAlphabet R.head).main)),
        mainTrackTriple (Turing.Tape.mk' L (encodeBlankSide R)),
        Turing.Tape.mk' L (encodeBlankSide R)⟩ := by
  rw [mainTrackReader_step]
  have h := mainTrackReader_decodes L R
  change decodeMainTriple (mainTrackTriple (Turing.Tape.mk' L (encodeBlankSide R))).1
      (mainTrackTriple (Turing.Tape.mk' L (encodeBlankSide R))).2.1
      (mainTrackTriple (Turing.Tape.mk' L (encodeBlankSide R))).2.2 = _ at h
  rw [h]

#print axioms mainTrackReader_step
#print axioms mainTrackSegment_readBlock
#print axioms readBlock_side
#print axioms mainTrackReader_decodes
#print axioms mainTrackReader_side_step
end LambdaTuring
