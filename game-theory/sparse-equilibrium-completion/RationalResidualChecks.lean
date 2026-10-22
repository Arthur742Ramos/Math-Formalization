/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalResidualSolver
public meta import RationalResidualSolver
public meta import RationalResidualCompletion
public meta import RationalLinearSolver
public meta import RationalOneVariableFintype
@[expose] public section
open SparseCompletion
#guard (rationalResidualCompletion (fun _ : Fin 0 => 0) (fun _ => 0) (-1) (-1)).isSome
#guard (rationalResidualCompletion (fun _ : Fin 1 => 1) (fun _ => 0) 1 0).map
  (fun B => B 0 0) = some 0
#guard rationalResidualCompletion (fun _ : Fin 1 => 1) (fun _ => 1) 1 0 = none
#guard rationalResidualCompletion (fun _ : Fin 1 => 1) (fun _ => 0) (-1) 0 = none
