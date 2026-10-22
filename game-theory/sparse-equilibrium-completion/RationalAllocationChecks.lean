/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalAllocationSearchSoundness
public import RationalIntervalInitializerChecks
public meta import RationalAllocationGrid
public meta import RationalAllocationRun
public meta import RationalFiniteSelection
public meta import RationalIntervalInitializerChecks
public meta import RationalIntervalInitializedAlgorithm
public meta import RationalIntervalInitialize
public meta import RationalIntervalConsistency
public meta import Mathlib.Data.List.MinMax
@[expose] public section
open SparseCompletion

#guard (rationalAllocationNodes 2 (1/2)).length=9
#guard (rationalAllocationNodes 0 (1/2)).length=1
#guard (rationalAllocationNodes 2 (1/2)).all
  (fun z => decide (0 ≤ rationalAnchorAllocation (fun _ => 0) (1/2) z 0))
#guard (rationalAllocationSearch (initializerTestParameters (1/4))
  (fun _ => 0) (fun _ => by norm_num) (1/2) (1/8)).isSome
#guard !(rationalAllocationSearch (initializerTestParameters (1/4))
  (fun _ => 2) (fun _ => by norm_num) (1/2) (1/8)).isSome
#guard (rationalReservoirSearch initializerNoResidual
  (fun _ => 0) (fun _ => by norm_num) (1/2) (1/8) 0).isSome
#guard (rationalReservoirSearch initializerNoResidual
  (fun _ => 0) (fun _ => by norm_num) (1/2) (1/8) 0).map
    (fun w => w.1 0)=some 1
#guard !(rationalAllocationSearch initializerEmpty
  Fin.elim0 (fun i => Fin.elim0 i) (1/2) (1/8)).isSome
