module
import Smirnov

open Set TopologicalSpace
universe u v

-- Empty spaces and arbitrary discrete spaces need no inhabitant or countability.
example {X : Type u} [TopologicalSpace X] [IsEmpty X] :
    Smirnov.LocallyMetrizable X := Smirnov.locallyMetrizable_of_metrizable

example {X : Type u} [TopologicalSpace X] [DiscreteTopology X] :
    ParacompactSpace X ∧ Smirnov.LocallyMetrizable X :=
  (Smirnov.metrizable_iff.mp inferInstance).2

-- The cover index and underlying space occupy independent universes.
example {X : Type u} {I : Type v} [TopologicalSpace X] [ParacompactSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hpf : ∀ x, {i | x ∈ U i}.Finite) (hmet : ∀ i, MetrizableSpace (U i)) :
    NagataSmirnov.HasSigmaLocallyFiniteBasis X :=
  Smirnov.exists_sigmaLocallyFiniteBasis_of_pointFinite_open_cover U hU hcover hpf hmet

example {X : Type u} [t : TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (h : Smirnov.LocallyMetrizable X) :
    ∃ m : MetricSpace X, m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = t :=
  Smirnov.compatible_metric_iff.mpr ⟨inferInstance, inferInstance, h⟩

-- Separation is a conclusion in the unrestricted criterion, not silently implicit.
example {X : Type u} [TopologicalSpace X] (h : MetrizableSpace X) : T2Space X :=
  (Smirnov.metrizable_iff.mp h).1
