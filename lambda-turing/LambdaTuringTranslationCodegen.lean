/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

This compiles calls to both public translators behind a runtime Boolean. The
false branch does not materialize the generated lambda term or machine table.
The probe is a code-generation check, not a full dependency-closure proof or a
practical time/space bound. A separate noncomputable negative control is needed.
-/
module

public import LambdaTuringSolution
public meta import LambdaTuringSolution

@[expose] public section

namespace LambdaTuring

def lambdaTranslationCodegen (request : Bool) (t : Term) : Bool :=
  if request then (lambdaToUnaryMachine t).table.isEmpty else true

def packagedTranslationCodegen (request : Bool) (t : Term) : Bool :=
  if request then (packagedLambdaToMachine t).2.table.isEmpty else true

def machineTranslationCodegen {states : Nat} (request : Bool) (p : Machine.Program states) : Bool :=
  if request then
    match Machine.machineToLambda p with
    | .var _ => true
    | .abs _ => false
    | .app _ _ => false
  else true

#eval lambdaTranslationCodegen false (.abs (.var 0))
#eval packagedTranslationCodegen false (.abs (.var 0))
#eval machineTranslationCodegen false Machine.immediateHalt

#print axioms lambdaTranslationCodegen
#print axioms packagedTranslationCodegen
#print axioms machineTranslationCodegen
end LambdaTuring
