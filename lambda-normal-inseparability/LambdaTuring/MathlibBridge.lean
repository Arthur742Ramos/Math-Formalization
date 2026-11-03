/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable
public import Mathlib.Computability.TuringMachine.PostTuringMachine

@[expose] public section

namespace LambdaTuring.Machine

instance : Inhabited Symbol := ⟨.blank⟩

def mathTape (t : Tape) : Turing.Tape Symbol :=
  ⟨t.head, Turing.ListBlank.mk t.left, Turing.ListBlank.mk t.right⟩

def mathAction : Action → Turing.TM0.Stmt Symbol
  | .left => .move .left
  | .right => .move .right
  | .write s => .write s

def mathProgram {states : Nat} (p : Program states) :
    Turing.TM0.Machine Symbol (Fin (states + 1)) :=
  fun q s => (instruction p q s).map fun (q', a) => (q', mathAction a)

def mathConfig {states : Nat} (c : Config states) : Turing.TM0.Cfg Symbol (Fin (states + 1)) :=
  ⟨c.state, mathTape c.tape⟩

theorem mathTape_moveLeft (t : Tape) :
    mathTape (moveLeft t) = (mathTape t).move .left := by
  cases t with
  | mk left head right =>
    cases left <;> simp [mathTape, moveLeft, Turing.Tape.move]
    all_goals rfl

theorem mathTape_moveRight (t : Tape) :
    mathTape (moveRight t) = (mathTape t).move .right := by
  cases t with
  | mk left head right =>
    cases right <;> simp [mathTape, moveRight, Turing.Tape.move]
    all_goals rfl

theorem mathTape_perform (a : Action) (t : Tape) :
    mathTape (perform a t) =
      (match mathAction a with
       | .move d => (mathTape t).move d
       | .write s => (mathTape t).write s) := by
  cases a with
  | left => exact mathTape_moveLeft t
  | right => exact mathTape_moveRight t
  | write s => rfl

theorem math_step {states : Nat} (p : Program states) (c : Config states) :
    (step p c).map mathConfig = Turing.TM0.step (mathProgram p) (mathConfig c) := by
  cases c with
  | mk q t =>
    cases h : instruction p q t.head with
    | none => simp [step, mathProgram, mathConfig, Turing.TM0.step, mathTape, h]
    | some pair =>
      rcases pair with ⟨q', a⟩
      cases a with
      | left => simpa [step, mathProgram, mathConfig, Turing.TM0.step, mathTape, mathAction, perform, h]
          using mathTape_moveLeft t
      | right => simpa [step, mathProgram, mathConfig, Turing.TM0.step, mathTape, mathAction, perform, h]
          using mathTape_moveRight t
      | write s => simp [step, mathProgram, mathConfig, Turing.TM0.step, mathTape, mathAction,
          perform, Turing.Tape.write, h]
/-- The numerical decoder descends to Mathlib's blank-extension quotient. -/
def mathDecode (t : Turing.ListBlank Symbol) : Option Nat :=
  Turing.ListBlank.liftOn t decode (by
    intro a b h
    obtain ⟨n, rfl⟩ := h
    exact (decode_append_blanks a n).symm)

theorem mathDecode_mk (xs : List Symbol) : mathDecode (Turing.ListBlank.mk xs) = decode xs := rfl

theorem mathTape_output (t : Tape) :
    mathDecode (mathTape t).right₀ = decode (t.head :: t.right) := by
  simp [mathTape, Turing.Tape.right₀, mathDecode_mk]

theorem math_initial {states : Nat} (n : Nat) :
    mathConfig (initial n : Config states) = Turing.TM0.init (input n) := by
  simp [mathConfig, mathTape, initial, input, Turing.TM0.init, Turing.Tape.mk₁,
    Turing.Tape.mk₂, Turing.Tape.mk']
  all_goals rfl


theorem reaches_stateTransition {states : Nat} {p : Program states} {a b : Config states} :
    Reaches p a b ↔ StateTransition.Reaches (step p) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step hs _ ih => exact .head hs ih
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head hs _ ih => exact .step hs ih

theorem math_respects {states : Nat} (p : Program states) :
    StateTransition.Respects (step p) (Turing.TM0.step (mathProgram p))
      (fun a b => mathConfig a = b) := by
  apply StateTransition.fun_respects.mpr
  intro c
  unfold StateTransition.FRespects
  cases h : step p c with
  | none => simpa [h] using (math_step p c).symm
  | some d =>
    apply Relation.TransGen.single
    simpa [h] using (math_step p c).symm

theorem math_eval_configs {states : Nat} (p : Program states) (c : Config states) :
    StateTransition.eval (Turing.TM0.step (mathProgram p)) (mathConfig c) =
      mathConfig <$> StateTransition.eval (step p) c :=
  StateTransition.tr_eval' (step p) (Turing.TM0.step (mathProgram p)) mathConfig (math_respects p) c

/-- Numerical observation in Mathlib's TM0 model using the same input and decoder. -/
def MathYields {states : Nat} (p : Program states) (n m : Nat) : Prop :=
  ∃ output, output ∈ Turing.TM0.eval (mathProgram p) (input n) ∧ mathDecode output = some m

theorem math_yields_iff {states : Nat} (p : Program states) (n m : Nat) :
    MathYields p n m ↔ Yields p n m := by
  unfold MathYields Yields Turing.TM0.eval
  rw [← math_initial (states := states) n, math_eval_configs]
  simp only [Part.mem_map_iff, exists_exists_and_eq_and]
  constructor
  · rintro ⟨a, ha, hout⟩
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).1 ha
    obtain ⟨hr, hh⟩ := StateTransition.mem_eval.1 hc
    exact ⟨c, reaches_stateTransition.2 hr, hh, by simpa [mathConfig, mathTape_output] using hout⟩
  · rintro ⟨c, hr, hh, hout⟩
    refine ⟨mathConfig c, ?_, ?_⟩
    · exact (Part.mem_map_iff _).2 ⟨c, StateTransition.mem_eval.2 ⟨reaches_stateTransition.1 hr, hh⟩, rfl⟩
    · simpa [mathConfig, mathTape_output] using hout


/-- Convert a Mathlib TM0 action over this alphabet into a table action. -/
def actionOfMath : Turing.TM0.Stmt Symbol → Action
  | .move .left => .left
  | .move .right => .right
  | .write s => .write s

theorem mathAction_actionOfMath (a : Turing.TM0.Stmt Symbol) :
    mathAction (actionOfMath a) = a := by
  cases a with
  | move d => cases d <;> rfl
  | write s => rfl

/-- Every Mathlib TM0 over these finite states and symbols has an explicit table. -/
def tableOfMathlib {states : Nat} (p : Turing.TM0.Machine Symbol (Fin (states + 1))) :
    Program states :=
  tableOfFunction fun q s => (p q s).map fun (q', a) => (q', actionOfMath a)

theorem mathProgram_tableOfMathlib {states : Nat}
    (p : Turing.TM0.Machine Symbol (Fin (states + 1))) :
    mathProgram (tableOfMathlib p) = p := by
  funext q s
  simp only [mathProgram, tableOfMathlib, tableOfFunction_instruction]
  cases h : p q s with
  | none => simp
  | some pair =>
    rcases pair with ⟨q', a⟩
    simp [mathAction_actionOfMath]

theorem math_no_numerical_iff {states : Nat} (p : Program states) (n : Nat) :
    (∀ m, ¬ MathYields p n m) ↔ (∀ m, ¬ Yields p n m) := by
  simp only [math_yields_iff]

theorem tableOfMathlib_yields_iff {states : Nat}
    (p : Turing.TM0.Machine Symbol (Fin (states + 1))) (n m : Nat) :
    Yields (tableOfMathlib p) n m ↔
      ∃ output, output ∈ Turing.TM0.eval p (input n) ∧ mathDecode output = some m := by
  rw [← math_yields_iff]
  simp only [MathYields, mathProgram_tableOfMathlib]

#print axioms mathProgram_tableOfMathlib
#print axioms tableOfMathlib_yields_iff
#print axioms math_no_numerical_iff
#print axioms math_eval_configs
#print axioms math_yields_iff
#print axioms mathTape_moveLeft
#print axioms mathTape_moveRight
#print axioms math_step
#print axioms mathDecode_mk
#print axioms mathTape_output
#print axioms math_initial

end LambdaTuring.Machine
