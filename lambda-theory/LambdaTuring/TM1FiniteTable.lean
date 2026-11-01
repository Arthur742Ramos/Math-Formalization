/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The statement support construction follows Mathlib's PostTuringMachine.lean,
copyright 2018 Mario Carneiro, released under Apache 2.0.
-/
module

public import LambdaTuring.ThreeSymbolControl
public meta import LambdaTuring.ThreeSymbolControl

@[expose] public section

namespace LambdaTuring

section GenericStatementEquality

variable {Γ Λ σ : Type} [Fintype Γ] [Fintype σ]
  [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]

/-- Structural equality of statements, comparing their embedded functions on
    the finite alphabet and finite store. -/
def finiteTM1StmtEq : DecidableEq (Turing.TM1.Stmt Γ Λ σ)
  | .move d q, .move d' q' =>
    letI : Decidable (q = q') := finiteTM1StmtEq q q'
    decidable_of_iff' (d = d' ∧ q = q') (by simp)
  | .write f q, .write f' q' =>
    letI : Decidable (q = q') := finiteTM1StmtEq q q'
    decidable_of_iff' ((∀ a s, f a s = f' a s) ∧ q = q') (by simp [funext_iff])
  | .load f q, .load f' q' =>
    letI : Decidable (q = q') := finiteTM1StmtEq q q'
    decidable_of_iff' ((∀ a s, f a s = f' a s) ∧ q = q') (by simp [funext_iff])
  | .branch f q r, .branch f' q' r' =>
    letI : Decidable (q = q') := finiteTM1StmtEq q q'
    letI : Decidable (r = r') := finiteTM1StmtEq r r'
    decidable_of_iff' ((∀ a s, f a s = f' a s) ∧ q = q' ∧ r = r') (by simp [funext_iff])
  | .goto f, .goto f' =>
    decidable_of_iff' (∀ a s, f a s = f' a s) (by simp [funext_iff])
  | .halt, .halt => .isTrue rfl
  | .move .., .write .. | .move .., .load .. | .move .., .branch .. | .move .., .goto ..
  | .move .., .halt | .write .., .move .. | .write .., .load .. | .write .., .branch ..
  | .write .., .goto .. | .write .., .halt | .load .., .move .. | .load .., .write ..
  | .load .., .branch .. | .load .., .goto .. | .load .., .halt | .branch .., .move ..
  | .branch .., .write .. | .branch .., .load .. | .branch .., .goto .. | .branch .., .halt
  | .goto .., .move .. | .goto .., .write .. | .goto .., .load .. | .goto .., .branch ..
  | .goto .., .halt | .halt, .move .. | .halt, .write .. | .halt, .load ..
  | .halt, .branch .. | .halt, .goto .. => .isFalse (by intro h; cases h)

end GenericStatementEquality

def tm1SubstmtList {Γ Λ σ : Type} : Turing.TM1.Stmt Γ Λ σ → List (Turing.TM1.Stmt Γ Λ σ)
  | q@(.move _ r) => q :: tm1SubstmtList r
  | q@(.write _ r) => q :: tm1SubstmtList r
  | q@(.load _ r) => q :: tm1SubstmtList r
  | q@(.branch _ r s) => q :: (tm1SubstmtList r ++ tm1SubstmtList s)
  | q => [q]

theorem tm1SubstmtList_mem {Γ Λ σ : Type} (q x : Turing.TM1.Stmt Γ Λ σ) :
    x ∈ tm1SubstmtList q ↔ x ∈ Turing.TM1.stmts₁ q := by
  classical
  induction q <;> simp [tm1SubstmtList, Turing.TM1.stmts₁, *]

section FiniteTM1Extraction

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
  [Fintype Γ] [Fintype Λ] [Fintype σ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ]

abbrev TM1RawState (Γ Λ σ : Type) := Option (Turing.TM1.Stmt Γ Λ σ) × σ

def tm1RawInitial (M : Λ → Turing.TM1.Stmt Γ Λ σ) : TM1RawState Γ Λ σ :=
  (some (M default), default)

def tm1RawMachine (M : Λ → Turing.TM1.Stmt Γ Λ σ) :
    TM1RawState Γ Λ σ → Γ → Option (TM1RawState Γ Λ σ × Turing.TM0.Stmt Γ) :=
  Turing.TM1to0.tr M

/-- Explicit list enumeration. Duplicates are retained to avoid noncomputable
    `Finset.toList` or any arbitrary ordering. -/
def tm1RawTail (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    List (TM1RawState Γ Λ σ) :=
  (none :: (labels.flatMap fun l => tm1SubstmtList (M l)).map some).flatMap
    fun q => stores.map fun s => (q, s)

def tm1RawList (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    List (TM1RawState Γ Λ σ) := tm1RawInitial M :: tm1RawTail M labels stores

omit [Inhabited Γ] [Inhabited σ] [Fintype Γ] [Fintype σ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] in
theorem tm1_supports_univ (M : Λ → Turing.TM1.Stmt Γ Λ σ) : Turing.TM1.Supports M Finset.univ := by
  classical
  have hall : ∀ q : Turing.TM1.Stmt Γ Λ σ, Turing.TM1.SupportsStmt Finset.univ q := by
    intro q
    induction q <;> simp [Turing.TM1.SupportsStmt, *]
  exact ⟨by simp, fun l _ => hall (M l)⟩

omit [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] in
set_option backward.isDefEq.respectTransparency false in
theorem tm1RawTail_mem (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (hl : ∀ l, l ∈ labels) (hs : ∀ s, s ∈ stores) (q : TM1RawState Γ Λ σ) :
    q ∈ tm1RawTail M labels stores ↔ q ∈ Turing.TM1to0.trStmts M Finset.univ := by
  classical
  rcases q with ⟨q, s⟩
  change (q, s) ∈ tm1RawTail M labels stores ↔
    (q, s) ∈ (Finset.insertNone (Finset.univ.biUnion fun l => Turing.TM1.stmts₁ (M l))) ×ˢ
      (Finset.univ : Finset σ)
  cases q <;> simp [tm1RawTail, tm1SubstmtList_mem, hl, hs]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem tm1Raw_supports (M : Λ → Turing.TM1.Stmt Γ Λ σ) :
    letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
    Turing.TM0.Supports (tm1RawMachine M)
      {q : TM1RawState Γ Λ σ | q ∈ Turing.TM1to0.trStmts M Finset.univ} := by
  classical
  letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
  exact Turing.TM1to0.tr_supports M (tm1_supports_univ M)

abbrev TM1NumberedState (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :=
  Fin (tm1RawList M labels stores).length

def tm1NumberInitial (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    TM1NumberedState M labels stores := ⟨0, by simp [tm1RawList]⟩

def tm1NumberRead (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (i : TM1NumberedState M labels stores) : TM1RawState Γ Λ σ :=
  (tm1RawList M labels stores).get i

def tm1NumberRaw (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (q : TM1RawState Γ Λ σ) : TM1NumberedState M labels stores := by
  letI : DecidableEq (Turing.TM1.Stmt Γ Λ σ) := finiteTM1StmtEq
  exact if h : q ∈ tm1RawList M labels stores then
    ⟨(tm1RawList M labels stores).idxOf q, List.idxOf_lt_length_iff.2 h⟩
  else tm1NumberInitial M labels stores

omit [Inhabited Γ] [Fintype Λ] in
set_option linter.style.haveILetI false in
theorem tm1NumberRead_raw (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (q : TM1RawState Γ Λ σ) (hq : q ∈ tm1RawList M labels stores) :
    tm1NumberRead M labels stores (tm1NumberRaw M labels stores q) = q := by
  letI : DecidableEq (Turing.TM1.Stmt Γ Λ σ) := finiteTM1StmtEq
  simp only [tm1NumberRaw, hq, ↓reduceDIte, tm1NumberRead, List.get_eq_getElem]
  exact List.getElem_idxOf _

omit [Inhabited Γ] [Fintype Λ] in
set_option linter.style.haveILetI false in
theorem tm1NumberRaw_initial (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    tm1NumberRaw M labels stores (tm1RawInitial M) = tm1NumberInitial M labels stores := by
  letI : DecidableEq (Turing.TM1.Stmt Γ Λ σ) := finiteTM1StmtEq
  apply Fin.ext
  simp [tm1NumberRaw, tm1RawList, tm1NumberInitial]

def tm1NumberedMachine (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    TM1NumberedState M labels stores → Γ →
      Option (TM1NumberedState M labels stores × Turing.TM0.Stmt Γ) :=
  fun i a => (tm1RawMachine M (tm1NumberRead M labels stores i) a).map
    (fun p => (tm1NumberRaw M labels stores p.1, p.2))

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] in
theorem tm1RawList_contains_support (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (hl : ∀ l, l ∈ labels) (hs : ∀ s, s ∈ stores) (q : TM1RawState Γ Λ σ)
    (hq : q ∈ Turing.TM1to0.trStmts M Finset.univ) : q ∈ tm1RawList M labels stores :=
  List.mem_cons_of_mem _ ((tm1RawTail_mem M labels stores hl hs q).2 hq)

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq σ] in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem tm1NumberRead_support (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (hl : ∀ l, l ∈ labels) (hs : ∀ s, s ∈ stores) (i : TM1NumberedState M labels stores) :
    tm1NumberRead M labels stores i ∈ Turing.TM1to0.trStmts M Finset.univ := by
  have hi : tm1NumberRead M labels stores i ∈ tm1RawList M labels stores := List.get_mem _ _
  simp only [tm1RawList, List.mem_cons] at hi
  rcases hi with h | h
  · rw [h]
    letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
    exact (tm1Raw_supports M).1
  · exact (tm1RawTail_mem M labels stores hl hs _).1 h

def genericPointedId : Turing.PointedMap Γ Γ := ⟨id, rfl⟩

omit [Fintype Γ] [DecidableEq Γ] in
theorem genericBlankSide_id (L : Turing.ListBlank Γ) : L.map genericPointedId = L := by
  induction L using Turing.ListBlank.induction_on with
  | h l => simp [genericPointedId]

theorem genericTape_id (T : Turing.Tape Γ) : T.map genericPointedId = T := by
  rcases T with ⟨a, l, r⟩
  simp only [Turing.Tape.map, genericBlankSide_id]
  rfl

set_option linter.style.haveILetI false in
def tm1NumberPointed (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
    letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
    Turing.PointedMap (TM1RawState Γ Λ σ) (TM1NumberedState M labels stores) := by
  letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
  letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
  exact ⟨tm1NumberRaw M labels stores, tm1NumberRaw_initial M labels stores⟩

omit [Fintype Λ] in
set_option linter.style.haveILetI false in
theorem tm1NumberedMachine_map (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ) :
    letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
    letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
    tm1NumberedMachine M labels stores = Turing.TM0.Machine.map (tm1RawMachine M)
      genericPointedId genericPointedId (tm1NumberRaw M labels stores) (tm1NumberRead M labels stores) := by
  letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
  letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
  funext i a
  simp only [tm1NumberedMachine, Turing.TM0.Machine.map, genericPointedId, id_eq]
  cases h : tm1RawMachine M (tm1NumberRead M labels stores i) a with
  | none => rfl
  | some p => rcases p with ⟨q, act⟩; cases act <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem tm1NumberedMachine_respects (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (hl : ∀ l, l ∈ labels) (hs : ∀ s, s ∈ stores) :
    letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
    letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
    StateTransition.Respects (Turing.TM0.step (tm1RawMachine M))
      (Turing.TM0.step (tm1NumberedMachine M labels stores))
      (fun a b => a.q ∈ Turing.TM1to0.trStmts M Finset.univ ∧
        Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw M labels stores) a = b) := by
  letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
  letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
  rw [tm1NumberedMachine_map]
  have h := Turing.TM0.Machine.map_respects (tm1RawMachine M) genericPointedId genericPointedId
    (tm1NumberPointed M labels stores) (tm1NumberRead M labels stores) (tm1Raw_supports M)
    (by intro a; rfl) (by
      intro q hq
      exact tm1NumberRead_raw M labels stores q (tm1RawList_contains_support M labels stores hl hs q hq))
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem tm1NumberedMachine_eval (M : Λ → Turing.TM1.Stmt Γ Λ σ) (labels : List Λ) (stores : List σ)
    (hl : ∀ l, l ∈ labels) (hs : ∀ s, s ∈ stores) (xs : List Γ) :
    letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
    Turing.TM0.eval (tm1NumberedMachine M labels stores) xs = Turing.TM1.eval M xs := by
  letI : Inhabited (TM1RawState Γ Λ σ) := ⟨tm1RawInitial M⟩
  letI : Inhabited (TM1NumberedState M labels stores) := ⟨tm1NumberInitial M labels stores⟩
  have hinit : (Turing.TM0.init xs : Turing.TM0.Cfg Γ (TM1RawState Γ Λ σ)).q ∈
      Turing.TM1to0.trStmts M Finset.univ ∧
      Turing.TM0.Cfg.map genericPointedId (tm1NumberRaw M labels stores)
        (Turing.TM0.init xs : Turing.TM0.Cfg Γ (TM1RawState Γ Λ σ)) =
          (Turing.TM0.init xs : Turing.TM0.Cfg Γ (TM1NumberedState M labels stores)) := by
    constructor
    · exact (tm1Raw_supports M).1
    · simp only [Turing.TM0.Cfg.map, Turing.TM0.init, genericTape_id]
      exact congrArg (fun q => Turing.TM0.Cfg.mk q (Turing.Tape.mk₁ xs)) (tm1NumberRaw_initial M labels stores)
  have heval : Turing.TM0.eval (tm1NumberedMachine M labels stores) xs = Turing.TM0.eval (tm1RawMachine M) xs := by
    apply Part.ext
    intro out
    simp only [Turing.TM0.eval, Part.mem_map_iff]
    constructor
    · rintro ⟨b, hb, hout⟩
      obtain ⟨a, ⟨_, hmap⟩, ha⟩ := StateTransition.tr_eval_rev (tm1NumberedMachine_respects M labels stores hl hs) hinit hb
      refine ⟨a, ha, ?_⟩
      rw [← hmap] at hout
      simpa [Turing.TM0.Cfg.map, genericTape_id] using hout
    · rintro ⟨a, ha, hout⟩
      obtain ⟨b, ⟨_, hmap⟩, hb⟩ := StateTransition.tr_eval (tm1NumberedMachine_respects M labels stores hl hs) hinit ha
      refine ⟨b, hb, ?_⟩
      rw [← hmap]
      simpa [Turing.TM0.Cfg.map, genericTape_id] using hout
  rw [heval]
  exact Turing.TM1to0.tr_eval M xs

end FiniteTM1Extraction

#print axioms finiteTM1StmtEq
#print axioms tm1SubstmtList_mem
#print axioms tm1Raw_supports
#print axioms tm1NumberedMachine_eval
end LambdaTuring
