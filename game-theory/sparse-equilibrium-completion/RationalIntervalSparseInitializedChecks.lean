/- AI-assisted executable controls. Apache-2.0. -/
module
public import RationalIntervalSparseInitialized
public import RationalIntervalSparseChecks
public meta import RationalIntervalSparseInitialized
public meta import RationalIntervalSparseApproximation
public meta import RationalIntervalSparseAlgorithm
public meta import RationalIntervalSparseChecks
public meta import RationalIntervalInitialize
public meta import RationalIntervalInitializerChecks
public meta import RationalLogRounds
public meta import RationalIntervalSearch
@[expose] public section
open SparseCompletion

def initializedSparseTest (floor : ℚ) :=
  rationalIntervalSparseInitialized (initializerTestParameters floor) (1/2)

#guard (initializedSparseTest (1/4)).isSome
#guard (initializedSparseTest (3/4)).isNone
#guard (initializedSparseTest (1/4)).all (fun o => decide (o.q 0=1/2))
#guard (initializedSparseTest (1/4)).all (fun o => decide (o.bracket.2-o.bracket.1 < 1/2))
#guard (initializedSparseTest (1/4)).all (fun o => decide (∀ i j,o.B i j=0))
#guard (rationalIntervalSparseInitialized initializerNoResidual (1/2)).isSome
#guard (rationalIntervalSparseInitialized initializerEmpty (1/2)).isNone
#guard (rationalIntervalSparseInitialized (initializerTestParameters (1/4)) 0).isSome
