/- Finite executable controls for actual graph-fuel direct execution. -/
module
public import RationalTableFlowPolynomial
public import DistanceControls
public meta import RationalTableFlowPolynomial
public meta import DistanceControls
public meta import RationalTableAugmentation
@[expose] public section
namespace SparseCompletion

#guard rationalTableGraphFuel (distanceControlCap 3) = 9

#guard rationalTableGraphFuel
  (distanceControlCap (100000000000000000000000000000000000000 / 7)) = 9

#guard rationalFlowTableEntry (rationalTableFindFlowPolynomial (distanceControlCap 3) 0 1) 0 1 = 3

#guard rationalFlowTableEntry
  (rationalTableFindFlowPolynomial (distanceControlCap 3) 0 0) 0 1 = 0

#guard rationalTableGraphFuel (distanceControlCap 0) = 1

#guard rationalFlowTableEntry (rationalTableFindFlowPolynomial (distanceControlCap 0) 0 1) 0 1 = 0

end SparseCompletion
