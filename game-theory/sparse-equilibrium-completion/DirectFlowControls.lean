module
public import RationalTableFlowDirect
public meta import RationalTableFlowDirect
@[expose] public section
open SparseCompletion
/- A huge numeric fuel must not build an unapplied continuation chain. -/
#guard rationalFlowTableEntry
  (rationalTableFlowIterateDirect (rationalZeroFlowTable 2) 0 1 100000000
    (rationalZeroFlowTable 2)) 0 1 = 0
#guard rationalFlowTableEntry
  (rationalTableFlowIterateDirect (rationalZeroFlowTable 2) 0 0 100000000
    (rationalZeroFlowTable 2)) 1 0 = 0
