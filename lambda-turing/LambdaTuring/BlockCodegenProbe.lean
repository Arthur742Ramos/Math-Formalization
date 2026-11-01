/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.BlockFiniteTM0
public meta import LambdaTuring.BlockFiniteTM0

@[expose] public section

namespace LambdaTuring

/-- Compile the table-construction branch without forcing its expensive value. -/
def tableCodegenProbe (request : Bool) : Bool :=
  if request then (blockProgram (compileListCodeTotal .zero)).table.isEmpty else true

#eval tableCodegenProbe false
#print axioms blockProgram
#print axioms blockTM0
#print axioms tm1NumberedMachine
#print axioms tm1RawList
#print axioms blockMachine
#print axioms blockStoreList
#print axioms compileListCodeTotal
end LambdaTuring
