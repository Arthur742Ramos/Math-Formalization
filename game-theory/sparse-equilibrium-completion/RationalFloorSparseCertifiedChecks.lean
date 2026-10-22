/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalFloorSparseCertified
public import RationalFloorSparseChecks
public meta import RationalFloorSparseCertified
public meta import RationalFloorSparseChecks
public meta import RationalFloorSparsify
public meta import RationalFloorAutomaticChecks
public meta import RationalIntervalInitializerChecks
@[expose] public section
open SparseCompletion

def globalCertifiedTest := rationalFloorSparseCertifiedApproximation (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) 1
#guard globalCertifiedTest.isSome
#guard globalCertifiedTest.map (fun v => v.2.bracket.2-v.2.bracket.1)=some 1
#guard globalCertifiedTest.map (fun v => decide (v.2.bracket.1 < 0 ∧ 0 ≤ v.2.bracket.2))=some true
#guard globalCertifiedTest.map (fun v => decide (v.1 0+v.2.q 0=1))=some true
#guard !(rationalFloorSparseCertifiedApproximation initializerEmpty Fin.elim0 (fun i => Fin.elim0 i) 1).isSome
#guard !(rationalFloorSparseCertifiedApproximation (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) 0).isSome
