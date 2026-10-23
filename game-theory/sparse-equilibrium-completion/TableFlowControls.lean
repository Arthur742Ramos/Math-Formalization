module
public import RationalTableFlowFuel
public meta import RationalTableFlowFuel
@[expose] public section
open SparseCompletion

def forwardUnitCapacity : RationalFlowTable 2 :=
  Vector.ofFn fun u => Vector.ofFn fun v => if u=0 ∧ v=1 then 1 else 0

def halfCapacity : RationalFlowTable 2 :=
  Vector.ofFn fun u => Vector.ofFn fun v => if u=0 ∧ v=1 then 1/2 else 0

def twoPathCapacity : RationalFlowTable 3 :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    if (u=0 ∧ v=1) ∨ (u=1 ∧ v=2) ∨ (u=0 ∧ v=2) then 1 else 0

#guard rationalFlowTableEntry (rationalTablePushPath (rationalZeroFlowTable 3) 0 [1,2] 1) 0 1 = 1
#guard rationalFlowTableEntry (rationalTablePushPath (rationalZeroFlowTable 3) 0 [1,2] 1) 1 0 = -1
#guard (rationalAugmentOnce forwardUnitCapacity (rationalZeroFlowTable 2) 0 1).map (fun out => out.amount) = some 1
#guard (rationalAugmentOnce forwardUnitCapacity (rationalZeroFlowTable 2) 1 0).isNone = true
#guard (rationalAugmentOnce forwardUnitCapacity (rationalZeroFlowTable 2) 0 0).isNone = true
#guard rationalTableFlowFuel forwardUnitCapacity 0 = 2
#guard rationalTableFlowValue (rationalTableFindFlow forwardUnitCapacity 0 1) 0 = 1
#guard rationalFlowTableEntry (rationalTableFindFlow forwardUnitCapacity 0 1) 1 0 = -1
#guard (rationalAugmentOnce forwardUnitCapacity (rationalTableFindFlow forwardUnitCapacity 0 1) 0 1).isNone = true
#guard rationalTableFlowValue (rationalTableFindFlow halfCapacity 0 1) 0 = 1/2
#guard rationalTableFlowValue (rationalTableFindFlow twoPathCapacity 0 2) 0 = 2
#guard rationalTableFlowValue (rationalTableFindFlow forwardUnitCapacity 0 0) 0 = 0
