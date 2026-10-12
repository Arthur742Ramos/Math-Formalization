module
import Metrization

open Set TopologicalSpace
open NagataSmirnov

-- Arbitrary discrete spaces, including uncountable ones, satisfy the criterion.
-- There is no Countable, SecondCountableTopology or SeparableSpace parameter.
example {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    HasSigmaLocallyFiniteBasis X := exists_sigmaLocallyFiniteBasis (X := X)

-- The empty-space boundary case requires no inhabitant or nonempty layer.
example {X : Type*} [TopologicalSpace X] [IsEmpty X] :
    HasSigmaLocallyFiniteBasis X := exists_sigmaLocallyFiniteBasis (X := X)

-- Regularity alone suffices for perfect normality; no T0 assumption is used.
example {X : Type*} [TopologicalSpace X] [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) : PerfectlyNormalSpace X :=
  h.perfectlyNormalSpace

-- The public result supplies an actual metric with exactly the given topology.
example {X : Type*} [t : TopologicalSpace X] [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) :
    ∃ m : MetricSpace X, m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = t :=
  compatible_metric_iff.mpr h

-- The metric conclusion itself supplies the required Hausdorff separation.
example {X : Type*} [TopologicalSpace X] [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) : T2Space X := by
  let := h.metrizableSpace
  infer_instance
