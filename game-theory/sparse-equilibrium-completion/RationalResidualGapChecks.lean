/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalResidualGap
public meta import RationalResidualGap
public meta import RationalResidualSolver
public meta import RationalResidualCompletion
public meta import RationalLinearSolver
public meta import RationalOneVariableFintype
@[expose] public section
open SparseCompletion
#guard (reconstructRationalGap (fun _ : Fin 0 => fun _ : Fin 1 => 0)
  (fun _ => 1) (fun _ => 0) 1 0 (1/100)).isSome
