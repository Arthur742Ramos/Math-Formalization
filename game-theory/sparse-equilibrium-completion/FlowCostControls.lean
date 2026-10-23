/- Exact finite source-event controls; untrusted evaluator checks, not bit time. -/
module
public import CountedFlowInitialization
public import DistanceControls
public meta import FlowComputationCost
public meta import CountedCachedBFS
public meta import CountedRationalPathOps
public meta import CountedAugmentCandidate
public meta import CountedRationalAugmentation
public meta import CountedFlowInitialization
public meta import DistanceControls
public meta import RationalTableAugmentation
public meta import CachedResidualBFS
@[expose] public section
namespace SparseCompletion

#guard (flowCountFinRange 3).1 = List.finRange 3
#guard flowWorkTotal (flowCountFinRange 3).2 = 7
#guard (flowCountVectorOfFn (fun _ : Fin 2 => ((0 : ℚ), ({} : FlowWork)))).1.get 1 = 0
#guard (flowCountVectorOfFn (fun _ : Fin 2 => ((0 : ℚ), ({} : FlowWork)))).2.vectorEvents = 2
#guard flowWorkTotal (flowCountVectorOfFn (fun _ : Fin 2 => ((0 : ℚ), ({} : FlowWork)))).2 = 9
#guard (flowCountResidualCache (distanceControlCap 3) distanceControlZero).2.rationalEvents = 8
#guard flowWorkTotal (flowCountResidualCache (distanceControlCap 3) distanceControlZero).2 = 55
#guard (flowCountBFSPath (flowCountResidualCache (distanceControlCap 3) distanceControlZero).1 0 1).1 = some [0, 1]
#guard flowWorkTotal (flowCountBFSPath (flowCountResidualCache (distanceControlCap 3) distanceControlZero).1 0 1).2 = 71
#guard flowWorkTotal (flowCountNodup ([0, 1] : List (Fin 2))).2 = 11
#guard (flowCountNodup ([0, 0] : List (Fin 2))).1 = false
#guard flowWorkTotal (flowCountNodup ([0, 0] : List (Fin 2))).2 = 10
#guard flowWorkTotal (flowCountAugmentCandidate (distanceControlCap 3) distanceControlZero 0 1 [0, 1]).2 = 40
#guard (flowCountPathBottleneck (distanceControlCap 3) distanceControlZero 0 [1]).1 = some 3
#guard flowWorkTotal (flowCountPathBottleneck (distanceControlCap 3) distanceControlZero 0 [1]).2 = 16
#guard flowWorkTotal (flowCountTablePushPath distanceControlZero 0 [1] 3).2 = 80
#guard flowWorkTotal (flowCountAugmentOnce (distanceControlCap 3) distanceControlZero 0 1).2 = 269
#guard (flowCountGraphFuel (distanceControlCap 3)).1 = 9
#guard flowWorkTotal (flowCountGraphFuel (distanceControlCap 3)).2 = 152
#guard flowWorkTotal (flowCountZeroTable 2).2 = 27
#guard rationalFlowTableEntry (flowCountFindFlowPolynomial (distanceControlCap 3) 0 1).1 0 1 = 3
#guard flowWorkTotal (flowCountFindFlowPolynomial (distanceControlCap 3) 0 1).2 = 598
#guard flowWorkTotal (flowCountFindFlowPolynomial
  (distanceControlCap (100000000000000000000000000000000000000 / 7)) 0 1).2 = 598
#guard flowWorkTotal (flowCountFindFlowPolynomial (distanceControlCap 3) 0 0).2 = 184
#guard (flowCountAppend ([0, 1] : List (Fin 2)) [0]).2.listEvents = 8
#guard (flowCountAppend ([0, 1] : List (Fin 2)) [0]).2.adminEvents = 6
#guard flowWorkTotal (flowCountAppend ([0, 1] : List (Fin 2)) [0]).2 = 14
#guard ((flowCountBFSExtendBuild
  (flowCountResidualCache (distanceControlCap 3) distanceControlZero).1
  (cachedBFSInitial 0) 1 [0]).1 ()).2.adminEvents = 7

end SparseCompletion
