/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import PointFiniteBasis

/-!
# Smirnov's local-to-global metrization theorem

A space is metrizable exactly when it is Hausdorff, paracompact, and locally
metrizable. Local patches and locally finite basis layers have arbitrary size.

References: Munkres, *Topology*, second edition, Theorem 42.1, pp. 261–262;
Sakai, *Geometric Aspects of General Topology*, second-edition manuscript,
Proposition 2.6.8(4), with the Hausdorff convention of Section 2.6.
-/

@[expose] public section

open Set TopologicalSpace

namespace Smirnov

variable {X I : Type*} [TopologicalSpace X]

/-- Every point has an open neighborhood whose inherited topology is metrizable. -/
def LocallyMetrizable (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U

theorem locallyMetrizable_of_metrizable [MetrizableSpace X] : LocallyMetrizable X := by
  intro x
  exact ⟨univ, isOpen_univ, mem_univ x, inferInstance⟩

/-- An arbitrary open cover by metrizable subspaces suffices in a paracompact
Hausdorff space. Neither the cover nor its members need be second countable. -/
theorem metrizable_of_open_cover [T2Space X] [ParacompactSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hmet : ∀ i, MetrizableSpace (U i)) : MetrizableSpace X := by
  classical
  obtain ⟨V, hVo, hVc, hVf, hVsub⟩ := precise_refinement U hU hcover
  have hVm : ∀ i, MetrizableSpace (V i) := by
    intro i
    let : MetrizableSpace (U i) := hmet i
    exact (Topology.IsEmbedding.inclusion (hVsub i)).metrizableSpace
  let : NormalSpace X := NormalSpace.of_paracompactSpace_r1Space (X := X)
  let : T3Space X := inferInstance
  exact (exists_sigmaLocallyFiniteBasis_of_pointFinite_open_cover
    V hVo hVc hVf.point_finite hVm).metrizableSpace

theorem LocallyMetrizable.metrizableSpace [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : MetrizableSpace X := by
  classical
  choose U hU hxU hmet using h
  exact metrizable_of_open_cover U hU
    (iUnion_eq_univ_iff.mpr fun x => ⟨x, hxU x⟩) hmet

/-- Smirnov's full criterion. Hausdorffness is explicit because Mathlib's
`ParacompactSpace` does not include it. -/
theorem metrizable_iff : MetrizableSpace X ↔
    T2Space X ∧ ParacompactSpace X ∧ LocallyMetrizable X := by
  constructor
  · intro h
    let : MetrizableSpace X := h
    let : MetricSpace X := metrizableSpaceMetric X
    exact ⟨inferInstance, inferInstance, locallyMetrizable_of_metrizable⟩
  · rintro ⟨hT2, hP, hL⟩
    let : T2Space X := hT2
    let : ParacompactSpace X := hP
    exact hL.metrizableSpace

/-- The criterion with the local condition expanded in the statement. -/
theorem metrizable_iff_explicit : MetrizableSpace X ↔
    T2Space X ∧ ParacompactSpace X ∧
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U :=
  metrizable_iff

/-- On a Hausdorff locally metrizable space, paracompactness is precisely the
remaining condition for a compatible metric. -/
theorem metrizable_iff_paracompact [T2Space X] (h : LocallyMetrizable X) :
    MetrizableSpace X ↔ ParacompactSpace X := by
  constructor
  · intro hM
    exact (metrizable_iff.mp hM).2.1
  · intro hP
    let : ParacompactSpace X := hP
    exact h.metrizableSpace

/-- A metric whose topology is the given topology. -/
@[instance_reducible]
noncomputable def compatibleMetric [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : MetricSpace X := by
  let : MetrizableSpace X := h.metrizableSpace
  exact metrizableSpaceMetric X

theorem compatibleMetric_topology [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : (compatibleMetric h).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) := by
  with_reducible_and_instances rfl

/-- Smirnov's criterion expressed by existence of an actual compatible metric. -/
theorem compatible_metric_iff :
    (∃ m : MetricSpace X,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X›) ↔
      T2Space X ∧ ParacompactSpace X ∧ LocallyMetrizable X := by
  constructor
  · rintro ⟨m, hm⟩
    let : MetricSpace X := m.replaceTopology hm.symm
    exact metrizable_iff.mp inferInstance
  · rintro ⟨hT2, hP, hL⟩
    let : T2Space X := hT2
    let : ParacompactSpace X := hP
    exact ⟨compatibleMetric hL, compatibleMetric_topology hL⟩

end Smirnov
