/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectLambdaEvaluator
public meta import LambdaTuring.DirectLambdaEvaluator

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- An explicit finite-machine translation of arbitrary lambda syntax. -/
def lambdaToUnaryMachine (t : Term) :=
  compiledUnaryMachine (Code.curry directLambdaEvaluatorCode (directTermNumber t))

theorem lambdaToUnaryMachine_correct (t : Term) (n m : Nat) :
    Machine.Yields (lambdaToUnaryMachine t) n m ↔ NumericalResult t n m := by
  rw [lambdaToUnaryMachine, compiledUnaryMachine_yields_iff,
    (compileLambdaTotal_sound (Code.curry directLambdaEvaluatorCode (directTermNumber t))).2 n,
    Code.eval_curry, directLambdaEvaluatorCode_eval, mem_numericalValue_iff]

theorem lambdaToUnaryMachine_no_result (t : Term) (n : Nat) :
    (∀ m, ¬ Machine.Yields (lambdaToUnaryMachine t) n m) ↔
      (∀ m, ¬ NumericalResult t n m) := by
  simp only [lambdaToUnaryMachine_correct]

/-- Both explicit syntax translations preserve every numerical result. -/
theorem explicitTranslations_correct (t : Term) {states : Nat} (p : Machine.Program states) :
    (∀ n m, Machine.Yields (lambdaToUnaryMachine t) n m ↔ NumericalResult t n m) ∧
    Scoped 0 (Machine.machineToLambda p) ∧
    (∀ n m, NumericalResult (Machine.machineToLambda p) n m ↔ Machine.Yields p n m) := by
  exact ⟨lambdaToUnaryMachine_correct t, (Machine.machineToLambda_correct p).1,
    (Machine.machineToLambda_correct p).2⟩

/-- The finite state count is packaged with the translated machine. -/
def packagedLambdaToMachine (t : Term) : Σ states, Machine.Program states :=
  ⟨_, lambdaToUnaryMachine t⟩

theorem packagedLambdaToMachine_correct (t : Term) (n m : Nat) :
    Machine.Yields (packagedLambdaToMachine t).2 n m ↔ NumericalResult t n m :=
  lambdaToUnaryMachine_correct t n m

theorem packagedLambdaToMachine_no_result (t : Term) (n : Nat) :
    (∀ m, ¬ Machine.Yields (packagedLambdaToMachine t).2 n m) ↔
      (∀ m, ¬ NumericalResult t n m) :=
  lambdaToUnaryMachine_no_result t n

theorem explicitPackagedTranslations_correct (t : Term) {states : Nat} (p : Machine.Program states) :
    (∀ n m, Machine.Yields (packagedLambdaToMachine t).2 n m ↔ NumericalResult t n m) ∧
    Scoped 0 (Machine.machineToLambda p) ∧
    (∀ n m, NumericalResult (Machine.machineToLambda p) n m ↔ Machine.Yields p n m) := by
  exact ⟨packagedLambdaToMachine_correct t, (Machine.machineToLambda_correct p).1,
    (Machine.machineToLambda_correct p).2⟩

/-- Exercise Lean's compiler on the translation branch without forcing its
    very large generated table. This is not a practical size bound. -/
def lambdaToUnaryMachineCodegenProbe (request : Bool) : Bool :=
  if request then (lambdaToUnaryMachine (.var 0)).table.isEmpty else true

#eval lambdaToUnaryMachineCodegenProbe false

#print axioms lambdaToUnaryMachine
#print axioms directLambdaEvaluatorCode
#print axioms compiledUnaryMachine
#print axioms lambdaToUnaryMachineCodegenProbe
#print axioms lambdaToUnaryMachine_correct
#print axioms explicitTranslations_correct
end LambdaTuring
