/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The support enumeration follows Mathlib/Computability/TuringMachine/ToPartrec.lean,
copyright 2020 Mario Carneiro, released under Apache 2.0.
The later simulator-support enumerations follow StackTuringMachine.lean and
PostTuringMachine.lean, copyright 2018 Mario Carneiro, released under Apache 2.0.
-/
module

public import LambdaTuring.FiniteExtraction
public meta import LambdaTuring.FiniteExtraction

@[expose] public section

namespace LambdaTuring

open Turing.PartrecToTM2

def stackStateList : List StackState := [none, some .consₗ, some .cons, some .bit0, some .bit1]

theorem stackStateList_complete (s : StackState) : s ∈ stackStateList := by
  cases s with
  | none => simp [stackStateList]
  | some s => cases s <;> simp [stackStateList]

/-- Enumerate the positions used inside a TM2 interpreter label. Duplicates
    are allowed so that no quotient choice or arbitrary ordering is needed. -/
def labelStmtList : StackLabel → List StackLabel
  | Q@(.move _ _ _ q) => Q :: labelStmtList q
  | Q@(.push _ _ q) => Q :: labelStmtList q
  | Q@(.read f) => Q :: stackStateList.flatMap (fun s => labelStmtList (f s))
  | Q@(.clear _ _ q) => Q :: labelStmtList q
  | Q@(.copy q) => Q :: labelStmtList q
  | Q@(.succ q) => Q :: unrev q :: labelStmtList q
  | Q@(.pred q r) => Q :: (labelStmtList q ++ (unrev r :: labelStmtList r))
  | Q@(.ret _) => [Q]

set_option backward.isDefEq.respectTransparency false in
theorem labelStmtList_mem (q x : StackLabel) : x ∈ labelStmtList q ↔ x ∈ trStmts₁ q := by
  classical
  induction q with
  | move p k₁ k₂ q ih | clear p k₁ q ih | copy q ih | push k₁ p q ih =>
    simp [labelStmtList, trStmts₁, ih]
  | read f ih =>
    simp [labelStmtList, trStmts₁, ih, stackStateList_complete]
  | succ q ih => simp [labelStmtList, trStmts₁, ih]
  | pred q r ihq ihr => simp [labelStmtList, trStmts₁, ihq, ihr, or_comm, or_assoc]
  | ret k => simp [labelStmtList, trStmts₁]

open Turing.PartrecToTM2.K'

/-- Direct list version of the interpreter's code support. -/
def codeLabelList : Turing.ToPartrec.Code → Cont' → List StackLabel
  | c@.zero', k => labelStmtList (trNormal c k)
  | c@.succ, k => labelStmtList (trNormal c k)
  | c@.tail, k => labelStmtList (trNormal c k)
  | c@(.cons f fs), k =>
    labelStmtList (trNormal c k) ++
      (codeLabelList f (.cons₁ fs k) ++
        (labelStmtList (move₂ (fun _ => false) main aux <|
          move₂ (fun s => s = Γ'.consₗ) stack main <|
            move₂ (fun _ => false) aux stack <| trNormal fs (.cons₂ k)) ++
          (codeLabelList fs (.cons₂ k) ++ labelStmtList (head stack <| .ret k))))
  | c@(.comp f g), k =>
    labelStmtList (trNormal c k) ++
      (codeLabelList g (.comp f k) ++ (labelStmtList (trNormal f k) ++ codeLabelList f k))
  | c@(.case f g), k => labelStmtList (trNormal c k) ++ (codeLabelList f k ++ codeLabelList g k)
  | c@(.fix f), k =>
    labelStmtList (trNormal c k) ++
      (codeLabelList f (.fix f k) ++
        (labelStmtList (.clear natEnd main <| trNormal f (.fix f k)) ++ [.ret k]))

set_option backward.isDefEq.respectTransparency false in
theorem codeLabelList_mem (c : Turing.ToPartrec.Code) (k : Cont') (x : StackLabel) :
    x ∈ codeLabelList c k ↔ x ∈ codeSupp' c k := by
  classical
  induction c generalizing k with
  | zero' | succ | tail => simp [codeLabelList, codeSupp', labelStmtList_mem]
  | cons f fs ihf ihfs => simp [codeLabelList, codeSupp', labelStmtList_mem, ihf, ihfs]
  | comp f g ihf ihg => simp [codeLabelList, codeSupp', labelStmtList_mem, ihf, ihg]
  | case f g ihf ihg => simp [codeLabelList, codeSupp', labelStmtList_mem, ihf, ihg]
  | fix f ih => simp [codeLabelList, codeSupp', labelStmtList_mem, ih, or_comm, or_assoc]

def tm2StmtList : ConcreteStmt2 → List SimLabel
  | .push k f q => .go k (.push f) q :: .ret q :: tm2StmtList q
  | .peek k f q => .go k (.peek f) q :: .ret q :: tm2StmtList q
  | .pop k f q => .go k (.pop f) q :: .ret q :: tm2StmtList q
  | .load _ q => tm2StmtList q
  | .branch _ q r => tm2StmtList q ++ tm2StmtList r
  | _ => []

theorem tm2StmtList_mem (q : ConcreteStmt2) (x : SimLabel) :
    x ∈ tm2StmtList q ↔ x ∈ concreteTM2Stmts q := by
  classical
  induction q <;> simp [tm2StmtList, concreteTM2Stmts, *]

def tm1LabelList (C : Turing.ToPartrec.Code) : List SimLabel :=
  (codeLabelList C .halt).flatMap fun l => .normal l :: tm2StmtList (Turing.PartrecToTM2.tr l)

set_option backward.isDefEq.respectTransparency false in
theorem tm1LabelList_mem (C : Turing.ToPartrec.Code) (x : SimLabel) :
    x ∈ tm1LabelList C ↔ x ∈ concreteTM1Labels C := by
  classical
  simp [tm1LabelList, concreteTM1Labels, tm2StmtList_mem, codeLabelList_mem,
    codeSupp, contSupp]

def tm1StmtList : ConcreteStmt1 → List ConcreteStmt1
  | Q@(.move _ q) => Q :: tm1StmtList q
  | Q@(.write _ q) => Q :: tm1StmtList q
  | Q@(.load _ q) => Q :: tm1StmtList q
  | Q@(.branch _ q r) => Q :: (tm1StmtList q ++ tm1StmtList r)
  | Q => [Q]

theorem tm1StmtList_mem (q : ConcreteStmt1) (x : ConcreteStmt1) :
    x ∈ tm1StmtList q ↔ x ∈ concreteTM1Stmts q := by
  classical
  induction q <;> simp [tm1StmtList, concreteTM1Stmts, *]

def rawStateList (C : Turing.ToPartrec.Code) : List RawTM0State :=
  (none :: ((tm1LabelList C).flatMap fun l => tm1StmtList (tm1ListInterpreter l)).map some).flatMap
    fun q => stackStateList.map fun s => (q, s)

set_option backward.isDefEq.respectTransparency false in
theorem rawStateList_mem (C : Turing.ToPartrec.Code) (q : RawTM0State) :
    q ∈ rawStateList C ↔ q ∈ concreteTM0Support C := by
  classical
  rcases q with ⟨q, s⟩
  cases q <;> simp [rawStateList, concreteTM0Support, tm1StmtList_mem, tm1LabelList_mem,
    stackStateList_complete]

#print axioms labelStmtList_mem
#print axioms codeLabelList_mem
#print axioms rawStateList_mem
end LambdaTuring
