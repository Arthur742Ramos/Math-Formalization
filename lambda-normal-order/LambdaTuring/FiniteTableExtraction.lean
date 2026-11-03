/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteSupportList
public meta import LambdaTuring.FiniteSupportList

@[expose] public section

namespace LambdaTuring

/-- The initial state is deliberately placed at index zero. Duplicate raw
    states are harmless: lookup always chooses the first occurrence. -/
def numberedStateList (C : Turing.ToPartrec.Code) : List RawTM0State :=
  tm0ListInitialState C :: rawStateList C

abbrev NumberedState (C : Turing.ToPartrec.Code) := Fin (numberedStateList C).length

def initialNumberedState (C : Turing.ToPartrec.Code) : NumberedState C :=
  ⟨0, by simp [numberedStateList]⟩

def readNumberedState (C : Turing.ToPartrec.Code) (i : NumberedState C) : RawTM0State :=
  (numberedStateList C).get i

def numberRawState (C : Turing.ToPartrec.Code) (q : RawTM0State) : NumberedState C :=
  if h : q ∈ numberedStateList C then
    ⟨(numberedStateList C).idxOf q, List.idxOf_lt_length_iff.2 h⟩
  else initialNumberedState C

theorem read_numberRawState (C : Turing.ToPartrec.Code) (q : RawTM0State)
    (hq : q ∈ numberedStateList C) : readNumberedState C (numberRawState C q) = q := by
  simp only [numberRawState, hq, ↓reduceDIte, readNumberedState, List.get_eq_getElem]
  exact List.getElem_idxOf _

theorem numberRawState_initial (C : Turing.ToPartrec.Code) :
    numberRawState C (tm0ListInitialState C) = initialNumberedState C := by
  apply Fin.ext
  simp [numberRawState, numberedStateList, initialNumberedState]

theorem rawState_support_member (C : Turing.ToPartrec.Code) (q : RawTM0State)
    (hq : q ∈ concreteTM0Support C) : q ∈ numberedStateList C := by
  exact List.mem_cons_of_mem _ ((rawStateList_mem C q).2 hq)

set_option linter.style.haveILetI false in
theorem numberedState_support (C : Turing.ToPartrec.Code) (i : NumberedState C) :
    readNumberedState C i ∈ concreteTM0Support C := by
  have hi : readNumberedState C i ∈ numberedStateList C := List.get_mem _ _
  simp only [numberedStateList, List.mem_cons] at hi
  rcases hi with h | h
  · rw [h]
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    exact (concreteTM0_supports C).1
  · exact (rawStateList_mem C _).1 h

/-- Computable finite-state transition function over the simulator's finite
    alphabet. The raw transition's target is looked up in the complete list. -/
def numberedMachine (C : Turing.ToPartrec.Code) :
    NumberedState C → SimAlphabet → Option (NumberedState C × Turing.TM0.Stmt SimAlphabet) :=
  fun i a => (tm0ListInterpreter C (readNumberedState C i) a).map
    (fun p => (numberRawState C p.1, p.2))

set_option linter.style.haveILetI false in
theorem numberedMachine_transition (C : Turing.ToPartrec.Code) (i : NumberedState C)
    (a : SimAlphabet) (q : RawTM0State) (act : Turing.TM0.Stmt SimAlphabet)
    (h : (q, act) ∈ tm0ListInterpreter C (readNumberedState C i) a) :
    (numberRawState C q, act) ∈ numberedMachine C i a ∧
      readNumberedState C (numberRawState C q) = q := by
  constructor
  · exact Option.mem_map.2 ⟨(q, act), h, rfl⟩
  · apply read_numberRawState
    apply rawState_support_member
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    exact (concreteTM0_supports C).2 h (numberedState_support C i)

def simAlphabetId : Turing.PointedMap SimAlphabet SimAlphabet := ⟨id, rfl⟩

theorem simAlphabet_listBlank_id (L : Turing.ListBlank SimAlphabet) :
    L.map simAlphabetId = L := by
  induction L using Turing.ListBlank.induction_on with
  | h l => simp [simAlphabetId]

theorem simAlphabet_tape_id (T : Turing.Tape SimAlphabet) : T.map simAlphabetId = T := by
  rcases T with ⟨a, l, r⟩
  simp only [Turing.Tape.map, simAlphabet_listBlank_id]
  rfl

set_option linter.style.haveILetI false in
def numberedStatePointed (C : Turing.ToPartrec.Code) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    Turing.PointedMap RawTM0State (NumberedState C) := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  exact ⟨numberRawState C, numberRawState_initial C⟩

set_option linter.style.haveILetI false in
theorem numberedMachine_map (C : Turing.ToPartrec.Code) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    numberedMachine C = Turing.TM0.Machine.map (tm0ListInterpreter C)
      simAlphabetId simAlphabetId (numberRawState C) (readNumberedState C) := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  funext i a
  simp only [numberedMachine, Turing.TM0.Machine.map, simAlphabetId, id_eq]
  cases h : tm0ListInterpreter C (readNumberedState C i) a with
  | none => rfl
  | some p =>
    rcases p with ⟨q, act⟩
    cases act <;> rfl

set_option linter.style.haveILetI false in
theorem numberedMachine_respects (C : Turing.ToPartrec.Code) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    StateTransition.Respects (Turing.TM0.step (tm0ListInterpreter C))
      (Turing.TM0.step (numberedMachine C))
      (fun a b => a.q ∈ concreteTM0Support C ∧
        Turing.TM0.Cfg.map simAlphabetId (numberRawState C) a = b) := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  rw [numberedMachine_map]
  have h := Turing.TM0.Machine.map_respects (tm0ListInterpreter C) simAlphabetId simAlphabetId
    (numberedStatePointed C) (readNumberedState C) (concreteTM0_supports C)
    (by intro a; rfl) (by
      intro q hq
      exact read_numberRawState C q (rawState_support_member C q hq))
  exact h

set_option linter.style.haveILetI false in
theorem numberedMachine_eval (C : Turing.ToPartrec.Code) (xs : List SimAlphabet) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    Turing.TM0.eval (numberedMachine C) xs = Turing.TM0.eval (tm0ListInterpreter C) xs := by
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  have hinit : (Turing.TM0.init xs : Turing.TM0.Cfg SimAlphabet RawTM0State).q ∈ concreteTM0Support C ∧
      Turing.TM0.Cfg.map simAlphabetId (numberRawState C)
        (Turing.TM0.init xs : Turing.TM0.Cfg SimAlphabet RawTM0State) =
          (Turing.TM0.init xs : Turing.TM0.Cfg SimAlphabet (NumberedState C)) := by
    constructor
    · exact (concreteTM0_supports C).1
    · simp only [Turing.TM0.Cfg.map, Turing.TM0.init, simAlphabet_tape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q (Turing.Tape.mk₁ xs)) (numberRawState_initial C)
  apply Part.ext
  intro out
  simp only [Turing.TM0.eval, Part.mem_map_iff]
  constructor
  · rintro ⟨b, hb, houtput⟩
    obtain ⟨a, ⟨_, hmap⟩, ha⟩ := StateTransition.tr_eval_rev (numberedMachine_respects C) hinit hb
    refine ⟨a, ha, ?_⟩
    rw [← hmap] at houtput
    simpa [Turing.TM0.Cfg.map, simAlphabet_tape_id] using houtput
  · rintro ⟨a, ha, houtput⟩
    obtain ⟨b, ⟨_, hmap⟩, hb⟩ := StateTransition.tr_eval (numberedMachine_respects C) hinit ha
    refine ⟨b, hb, ?_⟩
    rw [← hmap]
    simpa [Turing.TM0.Cfg.map, simAlphabet_tape_id] using houtput

/-- Build an alphabet symbol from its bottom marker and four stack tracks. -/
def makeSimAlphabet (b : Bool) (a r u s : StackState) : SimAlphabet :=
  (b, fun k => match k with
    | .main => a
    | .rev => r
    | .aux => u
    | .stack => s)

/-- An explicit enumeration of the finite simulation alphabet. -/
def simAlphabetList : List SimAlphabet :=
  [false, true].flatMap fun b =>
    stackStateList.flatMap fun a =>
      stackStateList.flatMap fun r =>
        stackStateList.flatMap fun u =>
          stackStateList.map fun s => makeSimAlphabet b a r u s

theorem simAlphabetList_complete (x : SimAlphabet) : x ∈ simAlphabetList := by
  rcases x with ⟨b, tracks⟩
  unfold simAlphabetList
  apply List.mem_flatMap.2
  refine ⟨b, by cases b <;> simp, ?_⟩
  apply List.mem_flatMap.2
  refine ⟨tracks .main, stackStateList_complete _, ?_⟩
  apply List.mem_flatMap.2
  refine ⟨tracks .rev, stackStateList_complete _, ?_⟩
  apply List.mem_flatMap.2
  refine ⟨tracks .aux, stackStateList_complete _, ?_⟩
  apply List.mem_map.2
  refine ⟨tracks .stack, stackStateList_complete _, ?_⟩
  unfold makeSimAlphabet
  congr 1
  funext k
  cases k <;> rfl

/-- Explicit transition entries for every numbered state and alphabet symbol. -/
def numberedTransitionTable (C : Turing.ToPartrec.Code) :
    List (NumberedState C × SimAlphabet × Option (NumberedState C × Turing.TM0.Stmt SimAlphabet)) :=
  (List.finRange (numberedStateList C).length).flatMap fun i =>
    simAlphabetList.map fun a => (i, a, numberedMachine C i a)

theorem numberedTransitionTable_complete (C : Turing.ToPartrec.Code)
    (i : NumberedState C) (a : SimAlphabet) :
    (i, a, numberedMachine C i a) ∈ numberedTransitionTable C := by
  apply List.mem_flatMap.2
  refine ⟨i, by simp, ?_⟩
  exact List.mem_map.2 ⟨a, simAlphabetList_complete a, rfl⟩

theorem numberedTransitionTable_sound (C : Turing.ToPartrec.Code)
    (i : NumberedState C) (a : SimAlphabet)
    (result : Option (NumberedState C × Turing.TM0.Stmt SimAlphabet))
    (h : (i, a, result) ∈ numberedTransitionTable C) : result = numberedMachine C i a := by
  obtain ⟨j, _, h⟩ := List.mem_flatMap.1 h
  obtain ⟨b, _, h⟩ := List.mem_map.1 h
  cases h
  rfl

/-- Data-only representation of a simulator tape symbol. -/
structure SimAlphabetData where
  bottom : Bool
  main : StackState
  rev : StackState
  aux : StackState
  stack : StackState
  deriving DecidableEq

def encodeSimAlphabet (a : SimAlphabet) : SimAlphabetData :=
  ⟨a.1, a.2 .main, a.2 .rev, a.2 .aux, a.2 .stack⟩

def decodeSimAlphabet (a : SimAlphabetData) : SimAlphabet :=
  makeSimAlphabet a.bottom a.main a.rev a.aux a.stack

theorem decode_encodeSimAlphabet (a : SimAlphabet) : decodeSimAlphabet (encodeSimAlphabet a) = a := by
  rcases a with ⟨b, tracks⟩
  unfold decodeSimAlphabet encodeSimAlphabet makeSimAlphabet
  congr 1
  funext k
  cases k <;> rfl

theorem encode_decodeSimAlphabet (a : SimAlphabetData) : encodeSimAlphabet (decodeSimAlphabet a) = a := by
  cases a
  rfl

def simAlphabetDataList : List SimAlphabetData := simAlphabetList.map encodeSimAlphabet

theorem simAlphabetDataList_complete (a : SimAlphabetData) : a ∈ simAlphabetDataList := by
  exact List.mem_map.2 ⟨decodeSimAlphabet a, simAlphabetList_complete _, encode_decodeSimAlphabet a⟩

def encodeSimAction : Turing.TM0.Stmt SimAlphabet → Turing.TM0.Stmt SimAlphabetData
  | .move d => .move d
  | .write a => .write (encodeSimAlphabet a)

def decodeSimAction : Turing.TM0.Stmt SimAlphabetData → Turing.TM0.Stmt SimAlphabet
  | .move d => .move d
  | .write a => .write (decodeSimAlphabet a)

theorem decode_encodeSimAction (a : Turing.TM0.Stmt SimAlphabet) :
    decodeSimAction (encodeSimAction a) = a := by
  cases a <;> simp [encodeSimAction, decodeSimAction, decode_encodeSimAlphabet]

def encodeNumberedTransition {C : Turing.ToPartrec.Code} :
    Option (NumberedState C × Turing.TM0.Stmt SimAlphabet) →
      Option (Nat × Turing.TM0.Stmt SimAlphabetData) :=
  Option.map fun p => (p.1.val, encodeSimAction p.2)

/-- A data-only finite transition table for the compiled numeric code.
    The input/output convention remains the encoded simulator convention. -/
def compileDataTable (c : Nat.Partrec.Code) :
    List (Nat × SimAlphabetData × Option (Nat × Turing.TM0.Stmt SimAlphabetData)) :=
  (numberedTransitionTable (compileListCodeTotal c)).map fun e =>
    (e.1.val, encodeSimAlphabet e.2.1, encodeNumberedTransition e.2.2)

theorem compileDataTable_complete (c : Nat.Partrec.Code)
    (i : NumberedState (compileListCodeTotal c)) (a : SimAlphabet) :
    (i.val, encodeSimAlphabet a,
      encodeNumberedTransition (numberedMachine (compileListCodeTotal c) i a)) ∈ compileDataTable c := by
  exact List.mem_map.2 ⟨(i, a, numberedMachine (compileListCodeTotal c) i a),
    numberedTransitionTable_complete (compileListCodeTotal c) i a, rfl⟩

theorem compileDataTable_sound (c : Nat.Partrec.Code) (q : Nat) (a : SimAlphabetData)
    (result : Option (Nat × Turing.TM0.Stmt SimAlphabetData))
    (h : (q, a, result) ∈ compileDataTable c) :
    ∃ i : NumberedState (compileListCodeTotal c), ∃ b : SimAlphabet,
      i.val = q ∧ encodeSimAlphabet b = a ∧
      encodeNumberedTransition (numberedMachine (compileListCodeTotal c) i b) = result := by
  obtain ⟨entry, he, hentry⟩ := List.mem_map.1 h
  rcases entry with ⟨i, b, r⟩
  have hr := numberedTransitionTable_sound (compileListCodeTotal c) i b r he
  subst r
  cases hentry
  exact ⟨i, b, rfl, rfl, rfl⟩

def dataTableLookup :
    List (Nat × SimAlphabetData × Option (Nat × Turing.TM0.Stmt SimAlphabetData)) →
      Nat → SimAlphabetData → Option (Option (Nat × Turing.TM0.Stmt SimAlphabetData))
  | [], _, _ => none
  | (q', a', r) :: rest, q, a =>
    if q' = q ∧ a' = a then some r else dataTableLookup rest q a

theorem dataTableLookup_of_consistent
    (rows : List (Nat × SimAlphabetData × Option (Nat × Turing.TM0.Stmt SimAlphabetData)))
    (q : Nat) (a : SimAlphabetData) (result : Option (Nat × Turing.TM0.Stmt SimAlphabetData))
    (hex : (q, a, result) ∈ rows)
    (hconsistent : ∀ r, (q, a, r) ∈ rows → r = result) :
    dataTableLookup rows q a = some result := by
  induction rows with
  | nil => simp at hex
  | cons row rows ih =>
    rcases row with ⟨q', a', r⟩
    by_cases h : q' = q ∧ a' = a
    · obtain ⟨rfl, rfl⟩ := h
      have hr : r = result := hconsistent r (by simp)
      simp [dataTableLookup, hr]
    · have htail : (q, a, result) ∈ rows := by
        simp only [List.mem_cons] at hex
        rcases hex with heq | heq
        · cases heq
          exact False.elim (h ⟨rfl, rfl⟩)
        · exact heq
      simp only [dataTableLookup, h, ↓reduceIte]
      apply ih htail
      intro r hr
      exact hconsistent r (List.mem_cons_of_mem _ hr)

theorem compileDataTable_lookup (c : Nat.Partrec.Code)
    (i : NumberedState (compileListCodeTotal c)) (a : SimAlphabet) :
    dataTableLookup (compileDataTable c) i.val (encodeSimAlphabet a) =
      some (encodeNumberedTransition (numberedMachine (compileListCodeTotal c) i a)) := by
  apply dataTableLookup_of_consistent
  · exact compileDataTable_complete c i a
  · intro r hr
    obtain ⟨j, b, hj, hb, hr⟩ := compileDataTable_sound c i.val (encodeSimAlphabet a) r hr
    have hij : j = i := Fin.ext hj
    have hab : b = a := by
      have h := congrArg decodeSimAlphabet hb
      simpa [decode_encodeSimAlphabet] using h
    subst j
    subst b
    exact hr.symm

def decodeNumberedTransition (C : Turing.ToPartrec.Code) :
    Option (Nat × Turing.TM0.Stmt SimAlphabetData) →
      Option (NumberedState C × Turing.TM0.Stmt SimAlphabet)
  | none => none
  | some (q, act) =>
    if h : q < (numberedStateList C).length then some (⟨q, h⟩, decodeSimAction act)
    else none

theorem decode_encodeNumberedTransition (C : Turing.ToPartrec.Code)
    (result : Option (NumberedState C × Turing.TM0.Stmt SimAlphabet)) :
    decodeNumberedTransition C (encodeNumberedTransition result) = result := by
  cases result with
  | none => rfl
  | some p =>
    rcases p with ⟨i, act⟩
    simp [encodeNumberedTransition, decodeNumberedTransition, i.isLt, decode_encodeSimAction]

/-- Interpret the concrete table by lookup. A missing row and a halting row
    are distinct in `dataTableLookup`; the former is unreachable for the
    compiled table by `compileDataTable_lookup`. -/
def compiledDataMachine (c : Nat.Partrec.Code) :
    NumberedState (compileListCodeTotal c) → SimAlphabet →
      Option (NumberedState (compileListCodeTotal c) × Turing.TM0.Stmt SimAlphabet) :=
  fun i a => (dataTableLookup (compileDataTable c) i.val (encodeSimAlphabet a)).bind
    (decodeNumberedTransition (compileListCodeTotal c))

theorem compiledDataMachine_eq (c : Nat.Partrec.Code) :
    compiledDataMachine c = numberedMachine (compileListCodeTotal c) := by
  funext i a
  simp [compiledDataMachine, compileDataTable_lookup, decode_encodeNumberedTransition]

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem numberedMachine_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (∃ out, out ∈ Turing.TM0.eval (numberedMachine C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  let C := compileListCodeTotal c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  change (∃ out, out ∈ Turing.TM0.eval (numberedMachine C) (tm0ListInput [n]) ∧
    tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n
  rw [numberedMachine_eval]
  exact compileListCodeTotal_lambda_tm0 c n m

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem numberedMachine_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (numberedMachine C) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  let C := compileListCodeTotal c
  letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
  letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
  change (¬ ∃ m out, out ∈ Turing.TM0.eval (numberedMachine C) (tm0ListInput [n]) ∧
    tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none
  rw [numberedMachine_eval]
  exact compileListCodeTotal_lambda_tm0_none c n

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem compiledDataMachine_lambda_result (c : Nat.Partrec.Code) (n m : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (∃ out, out ∈ Turing.TM0.eval (compiledDataMachine c) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ m ∈ numericalValue (compileLambdaTotal c) n := by
  rw [compiledDataMachine_eq]
  exact numberedMachine_lambda_result c n m

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem compiledDataMachine_lambda_none (c : Nat.Partrec.Code) (n : Nat) :
    let C := compileListCodeTotal c
    letI : Inhabited (NumberedState C) := ⟨initialNumberedState C⟩
    (¬ ∃ m out, out ∈ Turing.TM0.eval (compiledDataMachine c) (tm0ListInput [n]) ∧
      tm0DecodedNumber out = some m) ↔ numericalValue (compileLambdaTotal c) n = Part.none := by
  rw [compiledDataMachine_eq]
  exact numberedMachine_lambda_none c n

#eval simAlphabetList.length
#eval (numberedStateList Turing.ToPartrec.Code.zero').length
#eval ((numberedMachine Turing.ToPartrec.Code.zero'
  (initialNumberedState Turing.ToPartrec.Code.zero') default).map (fun p => p.1.val))

#print axioms numberedMachine_transition
#print axioms numberedMachine_respects
#print axioms numberedMachine_eval
#print axioms numberedTransitionTable_complete
#print axioms numberedMachine_lambda_result
#print axioms numberedMachine_lambda_none
#print axioms compileDataTable_complete
#print axioms compileDataTable_lookup
#print axioms compiledDataMachine_lambda_result
#print axioms compiledDataMachine_lambda_none
end LambdaTuring
