/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalCertifiedApproximation
public import RationalIntervalGameOutput
public meta import RationalLogRounds
public meta import RationalIntervalSolver
public meta import RationalAlgorithmCertificate
public meta import RationalIntervalEncoding
public meta import RationalIntervalForms
public meta import RationalIntervalVariables
public meta import RationalLinearForms
public meta import RationalIntervalRecovery
public meta import RationalResidualGap
public meta import RationalResidualSolver
public meta import RationalLinearSolver
public meta import RationalOneVariableFintype
public meta import RationalGrid
public meta import RationalCertificate
@[expose] public section
open SparseCompletion
#guard rationalLogRounds 1 (1/16)=5
#guard rationalLogRounds 0 (1/16)=1
#guard rationalLogRounds 1 2=1
#guard (rationalIntervalAlgorithm (k := 1) (m := 1)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 1/2) 1 (1/2) 0 (1/4)).isSome
#guard !(rationalIntervalAlgorithm (k := 1) (m := 1)
  (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 1/2) 1 (1/2) 0 (1/4)).isSome
#guard (rationalIntervalAlgorithm (k := 0) (m := 0)
  Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 1 0 0 (1/4)).isSome
#guard !(rationalIntervalAlgorithm (k := 0) (m := 0)
  Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 1 1 0 (1/4)).isSome
#guard (fullRationalCertificate (k := 1) (m := 1)
  (fun _ => 1/2) (fun _ => 1/2) (fun _ _ => 0)).check
    (fun _ _ => 0) (fun _ _ => 0) 1 0
#guard !(fullRationalCertificate (k := 1) (m := 1)
  (fun _ => 1/2) (fun _ => 1/2) (fun _ _ => 1)).check
    (fun _ _ => 0) (fun _ _ => 0) 1 0
