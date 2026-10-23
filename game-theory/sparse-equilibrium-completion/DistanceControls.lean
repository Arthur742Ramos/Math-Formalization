/- Narrow executable controls; no machine-runtime claim. -/
module
public import RationalAugmentationCount
public meta import RationalAugmentationCount
public meta import RationalTableAugmentation
public meta import CachedResidualDistance
@[expose] public section
namespace SparseCompletion

def distanceControlCap (q : ℚ) : RationalFlowTable 2 :=
  Vector.ofFn fun u => Vector.ofFn fun v => if u = 0 ∧ v = 1 then q else 0

def distanceControlZero : RationalFlowTable 2 :=
  Vector.ofFn fun _ => Vector.ofFn fun _ => 0

#guard (rationalAugmentOnce (distanceControlCap 3) distanceControlZero 0 1).map
  (fun out => out.path) = some [0, 1]

#guard (rationalAugmentOnce (distanceControlCap 3) distanceControlZero 0 1).map
  (fun out => out.amount) = some 3

#guard rationalFlowTableEntry (rationalTablePushPath distanceControlZero 0 [1] 3) 0 1 = 3

#guard rationalFlowTableEntry (rationalTablePushPath distanceControlZero 0 [1] 3) 1 0 = -3

#guard ((cacheResidualAdj (rationalFlowTableEntry (distanceControlCap 3))
  (rationalFlowTableEntry distanceControlZero)).get 1).get 0 = false

#guard ((cacheResidualAdj (rationalFlowTableEntry (distanceControlCap 3))
  (rationalFlowTableEntry (rationalTablePushPath distanceControlZero 0 [1] 3))).get 1).get 0 = true

#guard ((cacheResidualAdj (rationalFlowTableEntry (distanceControlCap 3))
  (rationalFlowTableEntry (rationalTablePushPath distanceControlZero 0 [1] 3))).get 0).get 1 = false

#guard cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry (distanceControlCap 3))
  (rationalFlowTableEntry distanceControlZero)) 0 1 = 1

#guard cachedBFSDistance (cacheResidualAdj (rationalFlowTableEntry (distanceControlCap 3))
  (rationalFlowTableEntry (rationalTablePushPath distanceControlZero 0 [1] 3))) 0 1 = 3

#guard rationalCapacityArcSupport (distanceControlCap 3) =
  rationalCapacityArcSupport (distanceControlCap (100000000000000000000000000000000000000 / 7))

end SparseCompletion
