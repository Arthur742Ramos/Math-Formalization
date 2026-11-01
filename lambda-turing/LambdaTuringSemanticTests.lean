/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuringSolution
public import LambdaTuring.Observation
public meta import LambdaTuring.Observation

@[expose] public section

#check LambdaTuring.lambdaComputable_iff_unaryMachine
#check LambdaTuring.packagedLambdaToMachine_correct
#check LambdaTuring.packagedLambdaToMachine_no_result
#check LambdaTuring.Machine.machineToLambda_correct
#check LambdaTuring.Machine.machineToLambda_no_result
#check LambdaTuring.explicitPackagedTranslations_correct
#check LambdaTuring.substAt
#check LambdaTuring.church
#check LambdaTuring.NumericalResult
#check LambdaTuring.Machine.instruction
#check LambdaTuring.Machine.step
#check LambdaTuring.Machine.decode
#check LambdaTuring.Machine.initial
#check LambdaTuring.Machine.Yields
#check LambdaTuring.packagedLambdaToMachine
#check LambdaTuring.Machine.machineToLambda

open LambdaTuring

example : Machine.decode [.mark] = none := rfl
example : Machine.decode [.one, .blank, .one] = none := rfl
example : Machine.decode [] = none := rfl
example : Machine.decode [.one] = some 0 := rfl
example (n m : Nat) : ¬ NumericalResult discardInput n m := discard_no_numeral n m
example (n m : Nat) : ¬ Machine.Yields Machine.markHalt n m := Machine.mark_no_numerical_result n m
