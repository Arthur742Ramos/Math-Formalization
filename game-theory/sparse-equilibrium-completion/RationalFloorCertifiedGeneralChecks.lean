/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalFloorCertifiedGeneral
public import RationalFloorAutomaticChecks
public meta import RationalFloorCertifiedGeneral
public meta import RationalFloorAutomaticChecks
public meta import RationalIntervalInitializerChecks
@[expose] public section
open SparseCompletion

def positiveFloorCertifiedTest := rationalFloorCertifiedApproximation (initializerTestParameters (3/4))
  (fun _ => 0) (fun _ => by norm_num) 1
#guard positiveFloorCertifiedTest.isSome
#guard positiveFloorCertifiedTest.map (fun v => v.2.bracket.2-v.2.bracket.1)=some 1
#guard positiveFloorCertifiedTest.map (fun v => decide (v.2.bracket.1 < 0 ∧ 0 ≤ v.2.bracket.2))=some true
#guard positiveFloorCertifiedTest.map (fun v => decide ((3/4 : ℚ) ≤ v.2.q 0))=some true
#guard positiveFloorCertifiedTest.map (fun v => decide (v.1 0+v.2.q 0=1))=some true
#guard !(rationalFloorCertifiedApproximation (initializerTestParameters (5/4))
  (fun _ => 0) (fun _ => by norm_num) 1).isSome
#guard !(rationalFloorCertifiedApproximation (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) 0).isSome
#guard !(rationalFloorCertifiedApproximation initializerEmpty Fin.elim0 (fun i => Fin.elim0 i) 1).isSome
