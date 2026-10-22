/- AI-assisted executable controls. Apache-2.0. -/
module
public import RationalIntervalSparseConditions
public import RationalIntervalInitializerChecks
public meta import RationalIntervalSparseAlgorithm
public meta import RationalFrozenPhysical
public meta import RationalSparseGapAlgorithm
public meta import RationalSparseGapSearch
public meta import RationalSparseSupport
public meta import RationalIntervalInitializerChecks
public meta import RationalIntervalRepertoireChecks
public meta import RationalAllocationGrid
public meta import RationalFiniteSelection
public meta import RationalGapDecision
public meta import RationalGapEncoding
public meta import RationalGap
public meta import RationalGrid
public meta import RationalResidualGap
public meta import RationalResidualSolver
public meta import RationalLinearSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def intervalSparseTest (floor : ℚ) :=
  let d := initializerTestParameters floor
  rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r 0 d.η d.R

#guard (intervalSparseTest (1/4)).isSome
#guard (intervalSparseTest (3/4)).isNone
#guard (intervalSparseTest (1/4)).all (fun w => decide (w.1 0=1/2))
#guard (intervalSparseTest (1/4)).all (fun w => decide (∀ a b,w.2.1 a b=0))
#guard (intervalSparseTest (1/4)).all (fun w => decide (∀ i a,w.2.2.1 i a=0))
#guard (intervalSparseTest (1/4)).all (fun w => decide (∀ i j,w.2.2.2 i j=0))

end SparseCompletion
