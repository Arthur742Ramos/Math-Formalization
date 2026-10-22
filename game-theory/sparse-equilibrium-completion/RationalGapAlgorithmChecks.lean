/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalGapValue
public meta import RationalGapValue
public meta import RationalGapAlgorithm
public meta import RationalGapSearch
public meta import RationalGapDecision
public meta import RationalResidualSolver
public meta import RationalLinearSolver
public meta import RationalOneVariableFintype
@[expose] public section
open SparseCompletion

def testNoRepertoire : RationalLinearSystem (Fin 0) 1 :=
  ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩

#guard (rationalGapAlgorithm (fun _ : Fin 1 => fun _ : Fin 1 => 0)
  (fun _ : Fin 1 => fun _ : Fin 1 => 1) (fun _ => 1/2)
  1 (1/2) (1/2) (1/4) testNoRepertoire).isSome
#guard rationalGapAlgorithm (fun _ : Fin 1 => fun _ : Fin 1 => 0)
  (fun _ : Fin 1 => fun _ : Fin 1 => 1) (fun _ => 1/2)
  1 (1/2) 0 (1/4) testNoRepertoire = none
#guard (rationalGapSearch (fun _ : Fin 1 => fun _ : Fin 1 => 0)
  (fun _ : Fin 1 => fun _ : Fin 1 => 1) (fun _ => 1/2)
  1 (1/2) (1/4) testNoRepertoire 2).2 -
  (rationalGapSearch (fun _ : Fin 1 => fun _ : Fin 1 => 0)
  (fun _ : Fin 1 => fun _ : Fin 1 => 1) (fun _ => 1/2)
  1 (1/2) (1/4) testNoRepertoire 2).1 = 1/4
