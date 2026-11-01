/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuringChallenge

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
example : substAt 0 (.var 0) (.abs (.app (.var 1) (.var 2))) =
    .abs (.app (.var 1) (.var 1)) := rfl
example : Beta (.abs (.app (.abs (.var 0)) (.var 0))) (.abs (.var 0)) :=
  .abs (.contract _ _)
