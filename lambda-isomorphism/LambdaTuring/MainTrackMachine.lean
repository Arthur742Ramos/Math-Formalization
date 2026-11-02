/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MainTrackReader
public meta import LambdaTuring.MainTrackReader

@[expose] public section

namespace LambdaTuring

def mainReaderLabels : List MainLabel :=
  [.start, .done none, .done (some none), .done (some (some .consₗ)),
    .done (some (some .cons)), .done (some (some .bit0)), .done (some (some .bit1))]

def mainReaderStores : List MainStore :=
  symbolList.flatMap fun a =>
    symbolList.flatMap fun b => symbolList.map fun c => (a,b,c)

theorem mainReaderLabels_complete (l : MainLabel) : l ∈ mainReaderLabels := by
  cases l with
  | start => simp [mainReaderLabels]
  | done o =>
    cases o with
    | none => simp [mainReaderLabels]
    | some s =>
      cases s with
      | none => simp [mainReaderLabels]
      | some s => cases s <;> simp [mainReaderLabels]

theorem mainReaderStores_complete (s : MainStore) : s ∈ mainReaderStores := by
  rcases s with ⟨a,b,c⟩
  exact List.mem_flatMap.2 ⟨a, symbolList_complete a,
    List.mem_flatMap.2 ⟨b, symbolList_complete b, List.mem_map.2 ⟨c, symbolList_complete c, rfl⟩⟩⟩

abbrev mainReaderStateCount := (tm1RawTail mainTrackReader mainReaderLabels mainReaderStores).length

def mainReaderTM0 :
    Fin (mainReaderStateCount + 1) → Machine.Symbol →
      Option (Fin (mainReaderStateCount + 1) × Turing.TM0.Stmt Machine.Symbol) :=
  tm1NumberedMachine mainTrackReader mainReaderLabels mainReaderStores

def mainReaderProgram : Machine.Program mainReaderStateCount :=
  Machine.tableOfMathlib mainReaderTM0

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem mainReaderProgram_eval (xs : List Machine.Symbol) :
    Turing.TM0.eval (Machine.mathProgram mainReaderProgram) xs =
      Turing.TM1.eval mainTrackReader xs := by
  letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
  letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
    ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
  have h : Machine.mathProgram mainReaderProgram = mainReaderTM0 := Machine.mathProgram_tableOfMathlib _
  rw [h]
  change Turing.TM0.eval (tm1NumberedMachine mainTrackReader mainReaderLabels mainReaderStores) xs = _
  exact tm1NumberedMachine_eval mainTrackReader mainReaderLabels mainReaderStores
    mainReaderLabels_complete mainReaderStores_complete xs

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem mainReader_numbered_reaches (t : Turing.Tape Machine.Symbol) :
    letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
    letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
      ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
    ∃ q, StateTransition.Reaches (Turing.TM0.step mainReaderTM0)
        ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores, t⟩ q ∧
      (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores q.q).2 = mainTrackTriple t ∧
      q.Tape = t := by
  letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
  letI : Inhabited (TM1RawState Machine.Symbol MainLabel MainStore) := ⟨tm1RawInitial mainTrackReader⟩
  letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
    ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
  let start : Turing.TM1.Cfg Machine.Symbol MainLabel MainStore := ⟨some .start, default, t⟩
  let last : Turing.TM1.Cfg Machine.Symbol MainLabel MainStore :=
    ⟨some (.done (decodeMainTriple (mainTrackTriple t).1 (mainTrackTriple t).2.1
      (mainTrackTriple t).2.2)), mainTrackTriple t, t⟩
  have hr : StateTransition.Reaches (Turing.TM1.step mainTrackReader) start last := by
    apply Relation.ReflTransGen.single
    simp [start, last, Turing.TM1.step, mainTrackReader_step]
  obtain ⟨raw, hraw, hreach⟩ := StateTransition.tr_reaches
    (Turing.TM1to0.tr_respects mainTrackReader) (show Turing.TM1to0.trCfg mainTrackReader start =
      Turing.TM1to0.trCfg mainTrackReader start from rfl) hr
  subst raw
  have hinit : (Turing.TM1to0.trCfg mainTrackReader start).q ∈
      Turing.TM1to0.trStmts mainTrackReader Finset.univ ∧
      Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw mainTrackReader mainReaderLabels mainReaderStores)
        (Turing.TM1to0.trCfg mainTrackReader start) =
      Turing.TM0.Cfg.mk (tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores) t := by
    constructor
    · change tm1RawInitial mainTrackReader ∈ Turing.TM1to0.trStmts mainTrackReader Finset.univ
      exact (tm1Raw_supports mainTrackReader).1
    · simp only [Turing.TM1to0.trCfg, start, Option.map_some, Turing.TM0.Cfg.map, genericTape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q t)
        (tm1NumberRaw_initial mainTrackReader mainReaderLabels mainReaderStores)
  obtain ⟨q, ⟨hsupport, hmap⟩, hq⟩ := StateTransition.tr_reaches
    (tm1NumberedMachine_respects mainTrackReader mainReaderLabels mainReaderStores
      mainReaderLabels_complete mainReaderStores_complete) hinit hreach
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hmap]
    simp only [Turing.TM0.Cfg.map]
    rw [tm1NumberRead_raw mainTrackReader mainReaderLabels mainReaderStores _]
    · rfl
    · exact tm1RawList_contains_support mainTrackReader mainReaderLabels mainReaderStores
        mainReaderLabels_complete mainReaderStores_complete _ hsupport
  · rw [← hmap]
    simp [Turing.TM0.Cfg.map, Turing.TM1to0.trCfg, genericTape_id, last]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem mainReader_numbered_reads (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) :
    letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
    letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
      ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
    ∃ q, StateTransition.Reaches (Turing.TM0.step mainReaderTM0)
        ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores,
          Turing.Tape.mk' L (encodeBlankSide R)⟩ q ∧
      (let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores q.q).2
       decodeMainTriple s.1 s.2.1 s.2.2 = some (encodeSimAlphabet R.head).main) ∧
      q.Tape = Turing.Tape.mk' L (encodeBlankSide R) := by
  let t := Turing.Tape.mk' L (encodeBlankSide R)
  obtain ⟨q, hr, hs, ht⟩ := mainReader_numbered_reaches t
  refine ⟨q, hr, ?_, ht⟩
  dsimp only
  rw [hs]
  have h := mainTrackReader_decodes L R
  change decodeMainTriple (mainTrackTriple t).1 (mainTrackTriple t).2.1
    (mainTrackTriple t).2.2 = _ at h
  exact h

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem mainReader_numbered_reaches_halted (t : Turing.Tape Machine.Symbol) :
    letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
    letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
      ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
    ∃ q, StateTransition.Reaches (Turing.TM0.step mainReaderTM0)
        ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores, t⟩ q ∧
      (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores q.q).2 = mainTrackTriple t ∧
      q.Tape = t ∧ Turing.TM0.step mainReaderTM0 q = none := by
  letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
  letI : Inhabited (TM1RawState Machine.Symbol MainLabel MainStore) := ⟨tm1RawInitial mainTrackReader⟩
  letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
    ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
  let start : Turing.TM1.Cfg Machine.Symbol MainLabel MainStore := ⟨some .start, default, t⟩
  let mid : Turing.TM1.Cfg Machine.Symbol MainLabel MainStore :=
    ⟨some (.done (decodeMainTriple (mainTrackTriple t).1 (mainTrackTriple t).2.1
      (mainTrackTriple t).2.2)), mainTrackTriple t, t⟩
  let last : Turing.TM1.Cfg Machine.Symbol MainLabel MainStore := ⟨none, mainTrackTriple t, t⟩
  have hr : StateTransition.Reaches (Turing.TM1.step mainTrackReader) start last := by
    apply Relation.ReflTransGen.head (b := mid)
    · simp [start, mid, Turing.TM1.step, mainTrackReader_step]
    · apply Relation.ReflTransGen.head (b := last)
      · simp [mid, last, Turing.TM1.step, Turing.TM1.stepAux, mainTrackReader]
      · exact Relation.ReflTransGen.refl
  obtain ⟨raw, hraw, hreach⟩ := StateTransition.tr_reaches
    (Turing.TM1to0.tr_respects mainTrackReader) (show Turing.TM1to0.trCfg mainTrackReader start =
      Turing.TM1to0.trCfg mainTrackReader start from rfl) hr
  subst raw
  have hinit : (Turing.TM1to0.trCfg mainTrackReader start).q ∈
      Turing.TM1to0.trStmts mainTrackReader Finset.univ ∧
      Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw mainTrackReader mainReaderLabels mainReaderStores)
        (Turing.TM1to0.trCfg mainTrackReader start) =
      Turing.TM0.Cfg.mk (tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores) t := by
    constructor
    · change tm1RawInitial mainTrackReader ∈ Turing.TM1to0.trStmts mainTrackReader Finset.univ
      exact (tm1Raw_supports mainTrackReader).1
    · simp only [Turing.TM1to0.trCfg, start, Option.map_some, Turing.TM0.Cfg.map, genericTape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q t)
        (tm1NumberRaw_initial mainTrackReader mainReaderLabels mainReaderStores)
  obtain ⟨q, ⟨hsupport, hmap⟩, hq⟩ := StateTransition.tr_reaches
    (tm1NumberedMachine_respects mainTrackReader mainReaderLabels mainReaderStores
      mainReaderLabels_complete mainReaderStores_complete) hinit hreach
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [← hmap]
    simp only [Turing.TM0.Cfg.map]
    rw [tm1NumberRead_raw mainTrackReader mainReaderLabels mainReaderStores _]
    · rfl
    · exact tm1RawList_contains_support mainTrackReader mainReaderLabels mainReaderStores
        mainReaderLabels_complete mainReaderStores_complete _ hsupport
  · rw [← hmap]
    simp [Turing.TM0.Cfg.map, Turing.TM1to0.trCfg, genericTape_id, last]
  · have hrawhalt : Turing.TM0.step (tm1RawMachine mainTrackReader)
        (Turing.TM1to0.trCfg mainTrackReader last) = none := by
      simp [tm1RawMachine, Turing.TM0.step, Turing.TM1to0.tr,
        Turing.TM1to0.trCfg, last]
    have hres := tm1NumberedMachine_respects mainTrackReader mainReaderLabels mainReaderStores
      mainReaderLabels_complete mainReaderStores_complete ⟨hsupport, hmap⟩
    rw [hrawhalt] at hres
    exact hres

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem mainReader_numbered_reads_halted (L : Turing.ListBlank Machine.Symbol)
    (R : Turing.ListBlank SimAlphabet) :
    letI : Fintype MainLabel := Fintype.ofList mainReaderLabels mainReaderLabels_complete
    letI : Inhabited (TM1NumberedState mainTrackReader mainReaderLabels mainReaderStores) :=
      ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores⟩
    ∃ q, StateTransition.Reaches (Turing.TM0.step mainReaderTM0)
        ⟨tm1NumberInitial mainTrackReader mainReaderLabels mainReaderStores,
          Turing.Tape.mk' L (encodeBlankSide R)⟩ q ∧
      (let s := (tm1NumberRead mainTrackReader mainReaderLabels mainReaderStores q.q).2
       decodeMainTriple s.1 s.2.1 s.2.2 = some (encodeSimAlphabet R.head).main) ∧
      q.Tape = Turing.Tape.mk' L (encodeBlankSide R) ∧ Turing.TM0.step mainReaderTM0 q = none := by
  let t := Turing.Tape.mk' L (encodeBlankSide R)
  obtain ⟨q, hr, hs, ht, hhalt⟩ := mainReader_numbered_reaches_halted t
  refine ⟨q, hr, ?_, ht, hhalt⟩
  dsimp only
  rw [hs]
  have h := mainTrackReader_decodes L R
  change decodeMainTriple (mainTrackTriple t).1 (mainTrackTriple t).2.1
    (mainTrackTriple t).2.2 = _ at h
  exact h

#eval mainReaderStores.length
#eval mainReaderStateCount
#print axioms mainReaderProgram_eval
#print axioms mainReader_numbered_reaches
#print axioms mainReader_numbered_reads
#print axioms mainReader_numbered_reaches_halted
#print axioms mainReader_numbered_reads_halted
end LambdaTuring
