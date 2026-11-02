/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ThreeSymbolCodec
public meta import LambdaTuring.ThreeSymbolCodec

@[expose] public section

namespace LambdaTuring

instance : Fintype Machine.Symbol :=
  Fintype.ofList [.blank, .one, .mark] (by intro s; cases s <;> simp)

instance : Fintype SimAlphabetData := Fintype.ofList simAlphabetDataList simAlphabetDataList_complete

abbrev BlockStore := Fin 13 → Machine.Symbol
abbrev BlockLabel (C : Turing.ToPartrec.Code) :=
  NumberedState C ⊕ (NumberedState C × SimAlphabetData)
abbrev BlockStmt (C : Turing.ToPartrec.Code) :=
  Turing.TM1.Stmt Machine.Symbol (BlockLabel C) BlockStore

def blockLabelList (C : Turing.ToPartrec.Code) : List (BlockLabel C) :=
  (List.finRange (numberedStateList C).length).map Sum.inl ++
    (List.finRange (numberedStateList C).length).flatMap fun i =>
      simAlphabetDataList.map fun a => Sum.inr (i, a)

instance (C : Turing.ToPartrec.Code) : Fintype (BlockLabel C) :=
  Fintype.ofList (blockLabelList C) (by
    intro l
    cases l with
    | inl i => simp [blockLabelList]
    | inr p => rcases p with ⟨i, a⟩; simp [blockLabelList, simAlphabetDataList_complete])

instance : Fintype BlockStore := inferInstance

def blockMoves {C : Turing.ToPartrec.Code} : Nat → Turing.Dir → BlockStmt C → BlockStmt C
  | 0, _, q => q
  | n+1, d, q => .move d (blockMoves n d q)

def blockWrites {C : Turing.ToPartrec.Code} : List Machine.Symbol → BlockStmt C → BlockStmt C
  | [], q => q
  | a :: xs, q => .write (fun _ _ => a) (.move .right (blockWrites xs q))

def blockReadStmts (C : Turing.ToPartrec.Code) (i : NumberedState C) :
    List (Fin 13) → BlockStmt C
  | [] => blockMoves 13 .left (.goto fun _ store =>
      .inr (i, (decodeSymbolBlock (List.ofFn store)).getD blankSimAlphabetData))
  | j :: js => .load (fun a store => Function.update store j a)
      (.move .right (blockReadStmts C i js))

def blockScan : List (Fin 13) → BlockStore → Turing.Tape Machine.Symbol →
    BlockStore × Turing.Tape Machine.Symbol
  | [], store, T => (store, T)
  | j :: js, store, T => blockScan js (Function.update store j T.head) (T.move .right)

theorem blockScan_tape (js : List (Fin 13)) (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    (blockScan js store T).2 = ((Turing.Tape.move Turing.Dir.right)^[js.length]) T := by
  induction js generalizing store T with
  | nil => rfl
  | cons j js ih => simp [blockScan, ih, Function.iterate_succ_apply]

theorem blockScan_preserves (js : List (Fin 13)) (store : BlockStore) (T : Turing.Tape Machine.Symbol)
    (j : Fin 13) (hj : j ∉ js) : (blockScan js store T).1 j = store j := by
  induction js generalizing store T with
  | nil => rfl
  | cons k js ih =>
    simp only [List.mem_cons, not_or] at hj
    simp [blockScan, ih _ _ hj.2, Function.update, hj.1]

theorem blockScan_read (js : List (Fin 13)) (store : BlockStore) (T : Turing.Tape Machine.Symbol)
    (j : Fin 13) (hj : j ∈ js) (hn : js.Nodup) :
    (blockScan js store T).1 j = ((Turing.Tape.move Turing.Dir.right)^[js.idxOf j] T).head := by
  induction js generalizing store T with
  | nil => simp at hj
  | cons k js ih =>
    simp only [List.nodup_cons] at hn
    by_cases h : j = k
    · subst j
      simp [blockScan, blockScan_preserves js _ _ k hn.1]
    · have hm : j ∈ js := by simpa [h] using hj
      have hidx : (k :: js).idxOf j = js.idxOf j + 1 := List.idxOf_cons_ne js (Ne.symm h)
      rw [hidx]
      simp only [blockScan]
      rw [ih _ _ hm hn.2]
      simp [Function.iterate_succ_apply]

theorem blockScan_full_store (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    (blockScan (List.finRange 13) store T).1 =
      fun j => ((Turing.Tape.move Turing.Dir.right)^[j.val] T).head := by
  funext j
  simpa using blockScan_read (List.finRange 13) store T j (by simp) (List.nodup_finRange 13)

theorem blockScan_full_tape (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    (blockScan (List.finRange 13) store T).2 = ((Turing.Tape.move Turing.Dir.right)^[13]) T := by
  simpa using blockScan_tape (List.finRange 13) store T

/-- Finite-control block simulator at Mathlib's TM1 level. The `.inl` phase
    reads a block; `.inr` executes the corresponding source transition. -/
def blockMachine (C : Turing.ToPartrec.Code) : BlockLabel C → BlockStmt C
  | .inl i => blockReadStmts C i (List.finRange 13)
  | .inr (i, data) =>
    match numberedMachine C i (decodeSimAlphabet data) with
    | none => .halt
    | some (j, .move d) => blockMoves 13 d (.goto fun _ _ => .inl j)
    | some (j, .write a) => blockWrites (encodeSimSymbol a)
        (blockMoves 13 .left (.goto fun _ _ => .inl j))

theorem blockMoves_stepAux (C : Turing.ToPartrec.Code) (n : Nat) (d : Turing.Dir)
    (q : BlockStmt C) (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    Turing.TM1.stepAux (blockMoves n d q) store T =
      Turing.TM1.stepAux q store ((Turing.Tape.move d)^[n] T) := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [blockMoves, Turing.TM1.stepAux, Function.iterate_succ_apply, ih]

theorem blockReadStmts_stepAux (C : Turing.ToPartrec.Code) (i : NumberedState C)
    (js : List (Fin 13)) (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    Turing.TM1.stepAux (blockReadStmts C i js) store T =
      ⟨some (.inr (i, (decodeSymbolBlock (List.ofFn (blockScan js store T).1)).getD blankSimAlphabetData)),
        (blockScan js store T).1, ((Turing.Tape.move Turing.Dir.left)^[13]) (blockScan js store T).2⟩ := by
  induction js generalizing store T with
  | nil => simp [blockReadStmts, blockScan, blockMoves_stepAux, Turing.TM1.stepAux]
  | cons j js ih => simp [blockReadStmts, blockScan, Turing.TM1.stepAux, ih]

theorem blockWrites_stepAux (C : Turing.ToPartrec.Code) (xs : List Machine.Symbol)
    (q : BlockStmt C) (store : BlockStore) (T : Turing.Tape Machine.Symbol) :
    Turing.TM1.stepAux (blockWrites xs q) store T =
      Turing.TM1.stepAux q store (writeBlock xs T) := by
  induction xs generalizing T with
  | nil => rfl
  | cons a xs ih => simp [blockWrites, writeBlock, Turing.TM1.stepAux, ih]

theorem blockMachine_read (C : Turing.ToPartrec.Code) (i : NumberedState C)
    (T : Turing.Tape SimAlphabet) (store : BlockStore) :
    Turing.TM1.stepAux (blockMachine C (.inl i)) store (encodeBlockTape T) =
      ⟨some (.inr (i, encodeSimAlphabet T.head)),
        (blockScan (List.finRange 13) store (encodeBlockTape T)).1, encodeBlockTape T⟩ := by
  have hstore : List.ofFn (blockScan (List.finRange 13) store (encodeBlockTape T)).1 =
      readBlock (encodeBlockTape T) := by
    rw [blockScan_full_store]
    rfl
  have hinv : Function.LeftInverse (Turing.Tape.move Turing.Dir.left : Turing.Tape Machine.Symbol → _)
      (Turing.Tape.move Turing.Dir.right) := Turing.Tape.move_right_left
  have htape : ((Turing.Tape.move Turing.Dir.left)^[13])
      (blockScan (List.finRange 13) store (encodeBlockTape T)).2 = encodeBlockTape T := by
    rw [blockScan_full_tape]
    exact (hinv.iterate 13) _
  change Turing.TM1.stepAux (blockReadStmts C i (List.finRange 13)) store (encodeBlockTape T) = _
  rw [blockReadStmts_stepAux, hstore, decode_readBlock_encodeBlockTape, htape]
  rfl

theorem blockMachine_execute_move (C : Turing.ToPartrec.Code)
    (i j : NumberedState C) (T : Turing.Tape SimAlphabet) (store : BlockStore) (d : Turing.Dir)
    (h : numberedMachine C i T.head = some (j, .move d)) :
    Turing.TM1.stepAux (blockMachine C (.inr (i, encodeSimAlphabet T.head))) store (encodeBlockTape T) =
      ⟨some (.inl j), store, encodeBlockTape (T.move d)⟩ := by
  cases d with
  | left => simp [blockMachine, decode_encodeSimAlphabet, h, blockMoves_stepAux,
      Turing.TM1.stepAux, ← encodeBlockTape_move_left]
  | right => simp [blockMachine, decode_encodeSimAlphabet, h, blockMoves_stepAux,
      Turing.TM1.stepAux, ← encodeBlockTape_move_right]

theorem blockMachine_execute_write (C : Turing.ToPartrec.Code)
    (i j : NumberedState C) (T : Turing.Tape SimAlphabet) (store : BlockStore) (a : SimAlphabet)
    (h : numberedMachine C i T.head = some (j, .write a)) :
    Turing.TM1.stepAux (blockMachine C (.inr (i, encodeSimAlphabet T.head))) store (encodeBlockTape T) =
      ⟨some (.inl j), store, encodeBlockTape (T.write a)⟩ := by
  simp [blockMachine, decode_encodeSimAlphabet, h, blockWrites_stepAux, blockMoves_stepAux,
    Turing.TM1.stepAux, ← encodeBlockTape_write]

theorem blockMachine_execute_halt (C : Turing.ToPartrec.Code)
    (i : NumberedState C) (T : Turing.Tape SimAlphabet) (store : BlockStore)
    (h : numberedMachine C i T.head = none) :
    Turing.TM1.stepAux (blockMachine C (.inr (i, encodeSimAlphabet T.head))) store (encodeBlockTape T) =
      ⟨none, store, encodeBlockTape T⟩ := by
  simp [blockMachine, decode_encodeSimAlphabet, h, Turing.TM1.stepAux]

/-- A source transition is simulated by a block-read step followed by an
    execute step, with no restriction on the incoming finite store. -/
theorem blockMachine_simulates_transition (C : Turing.ToPartrec.Code)
    (i j : NumberedState C) (T : Turing.Tape SimAlphabet) (store : BlockStore)
    (act : Turing.TM0.Stmt SimAlphabet) (h : numberedMachine C i T.head = some (j, act)) :
    ∃ store',
      Turing.TM1.step (blockMachine C) ⟨some (.inl i), store, encodeBlockTape T⟩ =
        some ⟨some (.inr (i, encodeSimAlphabet T.head)), store', encodeBlockTape T⟩ ∧
      Turing.TM1.step (blockMachine C)
        ⟨some (.inr (i, encodeSimAlphabet T.head)), store', encodeBlockTape T⟩ =
        some ⟨some (.inl j), store', encodeBlockTape (match act with
          | .move d => T.move d
          | .write a => T.write a)⟩ := by
  let store' := (blockScan (List.finRange 13) store (encodeBlockTape T)).1
  refine ⟨store', ?_, ?_⟩
  · change some (Turing.TM1.stepAux (blockMachine C (.inl i)) store (encodeBlockTape T)) = _
    rw [blockMachine_read]
  · change some (Turing.TM1.stepAux (blockMachine C (.inr (i, encodeSimAlphabet T.head))) store'
      (encodeBlockTape T)) = _
    cases act with
    | move d => rw [blockMachine_execute_move C i j T store' d h]
    | write a => rw [blockMachine_execute_write C i j T store' a h]

/-- On a source halt, the block machine reads the head, reaches a halting
    configuration, and preserves the encoded tape. -/
theorem blockMachine_simulates_halt (C : Turing.ToPartrec.Code)
    (i : NumberedState C) (T : Turing.Tape SimAlphabet) (store : BlockStore)
    (h : numberedMachine C i T.head = none) :
    ∃ store',
      Turing.TM1.step (blockMachine C) ⟨some (.inl i), store, encodeBlockTape T⟩ =
        some ⟨some (.inr (i, encodeSimAlphabet T.head)), store', encodeBlockTape T⟩ ∧
      Turing.TM1.step (blockMachine C)
        ⟨some (.inr (i, encodeSimAlphabet T.head)), store', encodeBlockTape T⟩ =
        some ⟨none, store', encodeBlockTape T⟩ ∧
      Turing.TM1.step (blockMachine C) ⟨none, store', encodeBlockTape T⟩ = none := by
  let store' := (blockScan (List.finRange 13) store (encodeBlockTape T)).1
  refine ⟨store', ?_, ?_, rfl⟩
  · change some (Turing.TM1.stepAux (blockMachine C (.inl i)) store (encodeBlockTape T)) = _
    rw [blockMachine_read]
  · change some (Turing.TM1.stepAux (blockMachine C (.inr (i, encodeSimAlphabet T.head))) store'
      (encodeBlockTape T)) = _
    rw [blockMachine_execute_halt C i T store' h]

abbrev BlockRawState (C : Turing.ToPartrec.Code) :=
  (NumberedState C × Turing.Tape SimAlphabet) ⊕ Turing.Tape SimAlphabet

/-- Add an explicit final state so the source and block-control machines both
    enter a terminal configuration after a positive number of steps. -/
def blockRawStep (C : Turing.ToPartrec.Code) : BlockRawState C → Option (BlockRawState C)
  | .inr _ => none
  | .inl (i, T) =>
    match numberedMachine C i T.head with
    | none => some (.inr T)
    | some (j, .move d) => some (.inl (j, T.move d))
    | some (j, .write a) => some (.inl (j, T.write a))

def blockStateRelation (C : Turing.ToPartrec.Code) :
    BlockRawState C → Turing.TM1.Cfg Machine.Symbol (BlockLabel C) BlockStore → Prop
  | .inl (i, T), target => ∃ store, target = ⟨some (.inl i), store, encodeBlockTape T⟩
  | .inr T, target => ∃ store, target = ⟨none, store, encodeBlockTape T⟩

theorem blockMachine_respects (C : Turing.ToPartrec.Code) :
    StateTransition.Respects (blockRawStep C) (Turing.TM1.step (blockMachine C))
      (blockStateRelation C) := by
  intro raw target hrel
  cases raw with
  | inr T =>
    obtain ⟨store, rfl⟩ := hrel
    rfl
  | inl p =>
    rcases p with ⟨i, T⟩
    obtain ⟨store, rfl⟩ := hrel
    cases h : numberedMachine C i T.head with
    | none =>
      obtain ⟨store', hread, hhalt, _⟩ := blockMachine_simulates_halt C i T store h
      simp only [blockRawStep, h]
      refine ⟨⟨none, store', encodeBlockTape T⟩, ⟨store', rfl⟩, ?_⟩
      exact Relation.TransGen.head hread (Relation.TransGen.single hhalt)
    | some result =>
      rcases result with ⟨j, act⟩
      obtain ⟨store', hread, hexec⟩ := blockMachine_simulates_transition C i j T store act h
      cases act with
      | move d =>
        simp only [blockRawStep, h]
        refine ⟨⟨some (.inl j), store', encodeBlockTape (T.move d)⟩, ⟨store', rfl⟩, ?_⟩
        exact Relation.TransGen.head hread (Relation.TransGen.single hexec)
      | write a =>
        simp only [blockRawStep, h]
        refine ⟨⟨some (.inl j), store', encodeBlockTape (T.write a)⟩, ⟨store', rfl⟩, ?_⟩
        exact Relation.TransGen.head hread (Relation.TransGen.single hexec)

def simTapeAction (a : Turing.TM0.Stmt SimAlphabet) (T : Turing.Tape SimAlphabet) :
    Turing.Tape SimAlphabet :=
  match a with
  | .move d => T.move d
  | .write s => T.write s

theorem blockRawStep_running (C : Turing.ToPartrec.Code) (i j : NumberedState C)
    (T : Turing.Tape SimAlphabet) (act : Turing.TM0.Stmt SimAlphabet)
    (h : numberedMachine C i T.head = some (j, act)) :
    blockRawStep C (.inl (i, T)) = some (.inl (j, simTapeAction act T)) := by
  cases act <;> simp [blockRawStep, simTapeAction, h]

def blockRawNormalize (C : Turing.ToPartrec.Code) (c : Turing.TM0.Cfg SimAlphabet (NumberedState C)) :
    BlockRawState C :=
  match numberedMachine C c.q c.Tape.head with
  | none => .inr c.Tape
  | some _ => .inl (c.q, c.Tape)

set_option linter.style.haveILetI false in
theorem blockRawNormalize_respects (C : Turing.ToPartrec.Code) :
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    StateTransition.Respects (Turing.TM0.step (numberedMachine C)) (blockRawStep C)
      (fun c r => blockRawNormalize C c = r) := by
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  intro c r hr
  subst r
  rcases c with ⟨i, T⟩
  cases h : numberedMachine C i T.head with
  | none => simp [Turing.TM0.step, blockRawNormalize, blockRawStep, h]
  | some p =>
    rcases p with ⟨j, act⟩
    have hstep : Turing.TM0.step (numberedMachine C) ⟨i, T⟩ =
        some ⟨j, simTapeAction act T⟩ := by
      cases act <;> simp [Turing.TM0.step, simTapeAction, h]
    rw [hstep]
    refine ⟨blockRawNormalize C ⟨j, simTapeAction act T⟩, rfl, ?_⟩
    have hfirst := blockRawStep_running C i j T act h
    rw [show blockRawNormalize C ⟨i, T⟩ = .inl (i, T) by simp [blockRawNormalize, h]]
    change StateTransition.Reaches₁ (blockRawStep C) (.inl (i, T))
      (blockRawNormalize C ⟨j, simTapeAction act T⟩)
    cases hnext : numberedMachine C j (simTapeAction act T).head with
    | none =>
      have hlast : blockRawStep C (.inl (j, simTapeAction act T)) =
          some (.inr (simTapeAction act T)) := by simp [blockRawStep, hnext]
      simp only [blockRawNormalize, hnext]
      exact Relation.TransGen.head hfirst (Relation.TransGen.single hlast)
    | some p =>
      simp only [blockRawNormalize, hnext]
      exact Relation.TransGen.single hfirst

def blockRawTape {C : Turing.ToPartrec.Code} : BlockRawState C → Turing.Tape SimAlphabet
  | .inl (_, T) => T
  | .inr T => T

theorem blockRawNormalize_tape (C : Turing.ToPartrec.Code)
    (c : Turing.TM0.Cfg SimAlphabet (NumberedState C)) :
    blockRawTape (blockRawNormalize C c) = c.Tape := by
  unfold blockRawNormalize
  cases numberedMachine C c.q c.Tape.head <;> rfl

theorem blockStateRelation_tape (C : Turing.ToPartrec.Code) (raw : BlockRawState C)
    (target : Turing.TM1.Cfg Machine.Symbol (BlockLabel C) BlockStore)
    (h : blockStateRelation C raw target) : target.Tape = encodeBlockTape (blockRawTape raw) := by
  cases raw with
  | inl p => rcases p with ⟨i, T⟩; obtain ⟨store, rfl⟩ := h; rfl
  | inr T => obtain ⟨store, rfl⟩ := h; rfl

set_option linter.style.haveILetI false in
theorem blockRaw_eval (C : Turing.ToPartrec.Code)
    (c : Turing.TM0.Cfg SimAlphabet (NumberedState C)) :
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    StateTransition.eval (blockRawStep C) (.inl (c.q, c.Tape)) =
      (StateTransition.eval (Turing.TM0.step (numberedMachine C)) c).map (blockRawNormalize C) := by
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  have hn := StateTransition.tr_eval' (Turing.TM0.step (numberedMachine C)) (blockRawStep C)
    (blockRawNormalize C) (blockRawNormalize_respects C) c
  have hp : StateTransition.eval (blockRawStep C) (.inl (c.q, c.Tape)) =
      StateTransition.eval (blockRawStep C) (blockRawNormalize C c) := by
    cases h : numberedMachine C c.q c.Tape.head with
    | some p => simp [blockRawNormalize, h]
    | none =>
      apply StateTransition.reaches_eval
      apply Relation.ReflTransGen.single
      simp [blockRawNormalize, blockRawStep, h]
  exact hp.trans hn

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Whole-run correspondence for the finite-control three-symbol machine on
    the block-encoded input; outputs remain block-encoded. -/
theorem blockMachine_eval (C : Turing.ToPartrec.Code) (xs : List SimAlphabet) :
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    Turing.TM1.eval (blockMachine C) (encodeSimSymbols xs) =
      (Turing.TM0.eval (numberedMachine C) xs).map encodeBlankSide := by
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  let source : Turing.TM0.Cfg SimAlphabet (NumberedState C) := Turing.TM0.init xs
  let raw : BlockRawState C := .inl (source.q, source.Tape)
  have hinit : blockStateRelation C raw (Turing.TM1.init (encodeSimSymbols xs)) := by
    refine ⟨default, ?_⟩
    change (⟨some (.inl (initialNumberedState C)), default, Turing.Tape.mk₁ (encodeSimSymbols xs)⟩ :
      Turing.TM1.Cfg Machine.Symbol (BlockLabel C) BlockStore) =
      ⟨some (.inl (initialNumberedState C)), default, encodeBlockTape (Turing.Tape.mk₁ xs)⟩
    rw [encodeBlockTape_initial]
  have hraw : StateTransition.eval (blockRawStep C) raw =
      (StateTransition.eval (Turing.TM0.step (numberedMachine C)) source).map (blockRawNormalize C) :=
    blockRaw_eval C source
  apply Part.ext
  intro out
  simp only [Turing.TM1.eval, Turing.TM0.eval, Part.map_map, Part.mem_map_iff]
  constructor
  · rintro ⟨b, hb, hout⟩
    obtain ⟨r, hrel, hr⟩ := StateTransition.tr_eval_rev (blockMachine_respects C) hinit hb
    rw [hraw] at hr
    obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).1 hr
    refine ⟨a, ha, ?_⟩
    have htape := blockStateRelation_tape C _ b hrel
    rw [blockRawNormalize_tape] at htape
    simpa [Function.comp_def, htape, encodeBlockTape_right] using hout
  · rintro ⟨a, ha, hout⟩
    have hr : blockRawNormalize C a ∈ StateTransition.eval (blockRawStep C) raw := by
      rw [hraw]
      exact (Part.mem_map_iff _).2 ⟨a, ha, rfl⟩
    obtain ⟨b, hrel, hb⟩ := StateTransition.tr_eval (blockMachine_respects C) hinit hr
    refine ⟨b, hb, ?_⟩
    have htape := blockStateRelation_tape C _ b hrel
    rw [blockRawNormalize_tape] at htape
    simpa [Function.comp_def, htape, encodeBlockTape_right] using hout

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- On the encoded input, the finite-control three-symbol machine has a
    block-encoded output exactly for each numerical lambda result. -/
theorem blockMachine_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    (∃ out sourceOut,
      out ∈ Turing.TM1.eval (blockMachine C) (encodeSimSymbols (tm0ListInput [n])) ∧
      out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔
        m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileListCodeTotal c
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  change (∃ out sourceOut,
    out ∈ Turing.TM1.eval (blockMachine C) (encodeSimSymbols (tm0ListInput [n])) ∧
    out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔
      m ∈ numericalValue (compileLambdaTotal c) n
  rw [blockMachine_eval]
  constructor
  · rintro ⟨out, sourceOut, hout, heq, hdecode⟩
    obtain ⟨sourceOut', hsource, hout'⟩ := (Part.mem_map_iff _).1 hout
    have he : sourceOut' = sourceOut := encodeBlankSide_injective (hout'.trans heq)
    subst sourceOut
    exact (numberedMachine_lambda_result c n m).1 ⟨sourceOut', hsource, hdecode⟩
  · intro hm
    obtain ⟨sourceOut, hsource, hdecode⟩ := (numberedMachine_lambda_result c n m).2 hm
    exact ⟨encodeBlankSide sourceOut, sourceOut, (Part.mem_map_iff _).2 ⟨sourceOut, hsource, rfl⟩,
      rfl, hdecode⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem blockMachine_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
    (¬ ∃ m out sourceOut,
      out ∈ Turing.TM1.eval (blockMachine C) (encodeSimSymbols (tm0ListInput [n])) ∧
      out = encodeBlankSide sourceOut ∧ tm0DecodedNumber sourceOut = some m) ↔
        numericalValue (compileLambdaTotal c) n = Part.none := by
  let C := compileListCodeTotal c
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  letI : Inhabited (BlockLabel C) := ⟨.inl (initialNumberedState C)⟩
  rw [Part.eq_none_iff]
  constructor
  · intro hnone m hm
    obtain ⟨out, sourceOut, hout, heq, hdecode⟩ := (blockMachine_lambda_result c n m).2 hm
    exact hnone ⟨m, out, sourceOut, hout, heq, hdecode⟩
  · rintro hnone ⟨m, out, sourceOut, hout, heq, hdecode⟩
    exact hnone m ((blockMachine_lambda_result c n m).1 ⟨out, sourceOut, hout, heq, hdecode⟩)

#print axioms blockMachine_execute_move
#print axioms blockMachine_execute_write
#print axioms blockMachine_read
#print axioms blockMachine_simulates_transition
#print axioms blockMachine_simulates_halt
#print axioms blockMachine_respects
#print axioms blockRawNormalize_respects
#print axioms blockMachine_eval
#print axioms blockMachine_lambda_result
#print axioms blockMachine_lambda_none
end LambdaTuring
