/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The finite-support constructions follow Mathlib's StackTuringMachine.lean and
PostTuringMachine.lean, copyright 2018 Mario Carneiro, released under Apache 2.0.
-/
module

public import LambdaTuring.ListCodeTotalCompiler
public meta import LambdaTuring.ListCodeTotalCompiler

@[expose] public section

namespace LambdaTuring

abbrev ConcreteStmt2 := Turing.TM2.Stmt (fun _ : StackIndex => StackSymbol) StackLabel StackState

def concreteStmt2DecidableEq : DecidableEq ConcreteStmt2
  | .push k f q, .push k' f' q' =>
    letI : Decidable (q = q') := concreteStmt2DecidableEq q q'
    decidable_of_iff' (k = k' ∧ f = f' ∧ q = q') (by simp)
  | .peek k f q, .peek k' f' q' =>
    letI : Decidable (q = q') := concreteStmt2DecidableEq q q'
    decidable_of_iff' (k = k' ∧ f = f' ∧ q = q') (by simp)
  | .pop k f q, .pop k' f' q' =>
    letI : Decidable (q = q') := concreteStmt2DecidableEq q q'
    decidable_of_iff' (k = k' ∧ f = f' ∧ q = q') (by simp)
  | .load f q, .load f' q' =>
    letI : Decidable (q = q') := concreteStmt2DecidableEq q q'
    decidable_of_iff' (f = f' ∧ q = q') (by simp)
  | .branch f q r, .branch f' q' r' =>
    letI : Decidable (q = q') := concreteStmt2DecidableEq q q'
    letI : Decidable (r = r') := concreteStmt2DecidableEq r r'
    decidable_of_iff' (f = f' ∧ q = q' ∧ r = r') (by simp)
  | .goto f, .goto f' => decidable_of_iff' (f = f') (by simp)
  | .halt, .halt => .isTrue rfl
  | .push .., .peek .. | .push .., .pop .. | .push .., .load .. | .push .., .branch ..
  | .push .., .goto .. | .push .., .halt | .peek .., .push .. | .peek .., .pop ..
  | .peek .., .load .. | .peek .., .branch .. | .peek .., .goto .. | .peek .., .halt
  | .pop .., .push .. | .pop .., .peek .. | .pop .., .load .. | .pop .., .branch ..
  | .pop .., .goto .. | .pop .., .halt | .load .., .push .. | .load .., .peek ..
  | .load .., .pop .. | .load .., .branch .. | .load .., .goto .. | .load .., .halt
  | .branch .., .push .. | .branch .., .peek .. | .branch .., .pop .. | .branch .., .load ..
  | .branch .., .goto .. | .branch .., .halt | .goto .., .push .. | .goto .., .peek ..
  | .goto .., .pop .. | .goto .., .load .. | .goto .., .branch .. | .goto .., .halt
  | .halt, .push .. | .halt, .peek .. | .halt, .pop .. | .halt, .load ..
  | .halt, .branch .. | .halt, .goto .. => .isFalse (by intro h; cases h)

instance : DecidableEq ConcreteStmt2 := concreteStmt2DecidableEq

abbrev ConcreteStAct (k : StackIndex) :=
  Turing.TM2to1.StAct StackIndex (fun _ => StackSymbol) StackState k

def concreteStActDecidableEq (k : StackIndex) : DecidableEq (ConcreteStAct k) := fun a b => by
  cases a <;> cases b
  case push.push f f' => exact decidable_of_iff' (f = f') (by simp)
  case peek.peek f f' => exact decidable_of_iff' (f = f') (by simp)
  case pop.pop f f' => exact decidable_of_iff' (f = f') (by simp)
  all_goals exact .isFalse (by intro h; cases h)

instance (k : StackIndex) : DecidableEq (ConcreteStAct k) := concreteStActDecidableEq k

def concreteSimLabelDecidableEq : DecidableEq SimLabel := fun a b => by
  cases a <;> cases b
  case normal.normal l l' => exact decidable_of_iff' (l = l') (by simp)
  case go.go k s q k' s' q' =>
    by_cases hk : k = k'
    · subst k'
      exact decidable_of_iff' (s = s' ∧ q = q') (by simp)
    · exact .isFalse (by intro h; cases h; exact hk rfl)
  case ret.ret q q' => exact decidable_of_iff' (q = q') (by simp)
  all_goals exact .isFalse (by intro h; cases h)

instance : DecidableEq SimLabel := concreteSimLabelDecidableEq

instance : Fintype StackIndex :=
  Fintype.ofList [.main, .rev, .aux, .stack] (by intro k; cases k <;> simp)

def stackVectorDecidableEq : DecidableEq (StackIndex → Option StackSymbol) := fun f g =>
  decidable_of_iff' (∀ k, f k = g k) (by simp [funext_iff])

instance : DecidableEq (StackIndex → Option StackSymbol) := stackVectorDecidableEq

instance : DecidableEq SimAlphabet :=
  show DecidableEq (Bool × (StackIndex → Option StackSymbol)) from inferInstance

abbrev ConcreteStmt1 := Turing.TM1.Stmt SimAlphabet SimLabel StackState

def concreteStmt1DecidableEq : DecidableEq ConcreteStmt1
  | .move d q, .move d' q' =>
    letI : Decidable (q = q') := concreteStmt1DecidableEq q q'
    decidable_of_iff' (d = d' ∧ q = q') (by simp)
  | .write f q, .write f' q' =>
    letI : Decidable (q = q') := concreteStmt1DecidableEq q q'
    decidable_of_iff' ((∀ a s, f a s = f' a s) ∧ q = q') (by simp [funext_iff])
  | .load f q, .load f' q' =>
    letI : Decidable (q = q') := concreteStmt1DecidableEq q q'
    decidable_of_iff' ((∀ a s, f a s = f' a s) ∧ q = q') (by simp [funext_iff])
  | .branch f q r, .branch f' q' r' =>
    letI : Decidable (q = q') := concreteStmt1DecidableEq q q'
    letI : Decidable (r = r') := concreteStmt1DecidableEq r r'
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

instance : DecidableEq ConcreteStmt1 := concreteStmt1DecidableEq

instance : DecidableEq RawTM0State := inferInstance

def concreteTM2Stmts : ConcreteStmt2 → Finset SimLabel
  | .push k f q => { .go k (.push f) q, .ret q } ∪ concreteTM2Stmts q
  | .peek k f q => { .go k (.peek f) q, .ret q } ∪ concreteTM2Stmts q
  | .pop k f q => { .go k (.pop f) q, .ret q } ∪ concreteTM2Stmts q
  | .load _ q => concreteTM2Stmts q
  | .branch _ q r => concreteTM2Stmts q ∪ concreteTM2Stmts r
  | _ => ∅

theorem concreteTM2Stmts_eq (q : ConcreteStmt2) :
    concreteTM2Stmts q = Turing.TM2to1.trStmts₁ q := by
  classical
  ext x
  induction q <;> simp [concreteTM2Stmts, Turing.TM2to1.trStmts₁, *]

def concreteTM1Labels (C : Turing.ToPartrec.Code) : Finset SimLabel :=
  (Turing.PartrecToTM2.codeSupp C Turing.PartrecToTM2.Cont'.halt).biUnion fun l =>
    insert (.normal l) (concreteTM2Stmts (Turing.PartrecToTM2.tr l))

def concreteTM1Stmts : ConcreteStmt1 → Finset ConcreteStmt1
  | Q@(.move _ q) => insert Q (concreteTM1Stmts q)
  | Q@(.write _ q) => insert Q (concreteTM1Stmts q)
  | Q@(.load _ q) => insert Q (concreteTM1Stmts q)
  | Q@(.branch _ q r) => insert Q (concreteTM1Stmts q ∪ concreteTM1Stmts r)
  | Q => {Q}

theorem concreteTM1Stmts_eq (q : ConcreteStmt1) :
    concreteTM1Stmts q = Turing.TM1.stmts₁ q := by
  classical
  ext x
  induction q <;> simp [concreteTM1Stmts, Turing.TM1.stmts₁, *]

/-- Executable construction of the exact finite support used by Mathlib's
    two simulations. Equality checks on embedded functions range over finite
    input types. -/
def concreteTM0Support (C : Turing.ToPartrec.Code) : Finset RawTM0State :=
  (Finset.insertNone ((concreteTM1Labels C).biUnion fun l => concreteTM1Stmts (tm1ListInterpreter l))) ×ˢ
    Finset.univ

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem concreteTM0Support_eq (C : Turing.ToPartrec.Code) :
    concreteTM0Support C = tm0ListSupport C := by
  classical
  letI : Inhabited StackLabel := ⟨Turing.PartrecToTM2.trNormal C Turing.PartrecToTM2.Cont'.halt⟩
  unfold concreteTM0Support tm0ListSupport Turing.TM1to0.trStmts Turing.TM1.stmts
  simp only [concreteTM1Stmts_eq]
  unfold concreteTM1Labels Turing.TM2to1.trSupp
  simp only [concreteTM2Stmts_eq]
  ext ⟨q, s⟩
  simp only [Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_insertNone,
    Finset.mem_biUnion, Finset.mem_insert]

theorem concreteTM0_supports (C : Turing.ToPartrec.Code) :
    letI : Inhabited RawTM0State := ⟨tm0ListInitialState C⟩
    Turing.TM0.Supports (tm0ListInterpreter C) ↑(concreteTM0Support C) := by
  rw [concreteTM0Support_eq]
  exact tm0List_supported C

#eval decide ((Turing.TM1.Stmt.halt : ConcreteStmt1) = .halt)
#eval decide ((Turing.TM1.Stmt.goto (fun _ _ => .normal (.ret .halt)) : ConcreteStmt1) =
  .goto (fun _ _ => .normal (.ret .halt)))

#print axioms concreteStmt2DecidableEq
#print axioms concreteSimLabelDecidableEq
#print axioms concreteStmt1DecidableEq
#print axioms concreteTM0_supports

end LambdaTuring
