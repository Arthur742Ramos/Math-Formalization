/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputEndToEnd
public meta import LambdaTuring.OutputEndToEnd

@[expose] public section

namespace LambdaTuring

/- This compiles the machine-construction branch but does not evaluate it.
It must not be read as a practical bound or full table materialization. -/
def unaryCompilerCodegenProbe (request : Bool) (c : Nat.Partrec.Code) : Bool :=
  if request then (compiledUnaryMachine c).table.isEmpty else true

#eval unaryCompilerCodegenProbe false .zero
#print axioms compileLambdaTotal
#print axioms compileUnaryOutputCode
#print axioms numberedMachine
#print axioms blockTM0
#print axioms blockProgram
#print axioms Machine.unaryOutputConverter
#print axioms unaryOnesProgram
#print axioms compiledUnaryMachine
#print axioms Machine.tableOfFunction
#print axioms Machine.tableOfMathlib
#print axioms tm1NumberedMachine
end LambdaTuring
