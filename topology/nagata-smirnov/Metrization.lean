/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import SigmaBasis
public import CompatibleMetric
public import MetricBasis
public import Mathlib.Topology.Separation.PerfectlyNormal

/-!
# Nagata–Smirnov metrization

The sigma locally finite basis is allowed arbitrary cardinality in every layer.
Perfect normality supplies cozero coordinates; local finiteness makes each
layer continuous for the uniform metric. A countable product of these metric
function spaces induces the given topology.

Reference: Katsuro Sakai, Geometric Aspects of General Topology, second-edition
manuscript (2023), Theorem 2.3.4(a),(c) and Lemma 2.3.3.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- A sigma locally finite cozero basis induces a topology from a countable
product of metric function spaces. Individual layers can be uncountable. -/
theorem pseudoMetrizable_of_cozero_basis
    (B : ℕ → Set (Set X))
    (hl : ∀ n, LocallyFinite (fun U : B n => (U : Set X)))
    (hb : IsTopologicalBasis (⋃ n, B n))
    (f : ∀ n, B n → C(X, ℝ))
    (hf : ∀ n U x, f n U x ∈ Icc (0 : ℝ) 1)
    (hzero : ∀ n U x, f n U x = 0 ↔ x ∉ (U : Set X)) :
    PseudoMetrizableSpace X := by
  classical
  let : ∀ n, TopologicalSpace (B n) := fun _ => ⊥
  have : ∀ n, DiscreteTopology (B n) := fun _ => ⟨rfl⟩
  have : PseudoMetrizableSpace (∀ n, B n →ᵇ ℝ) := inferInstance
  let F : X → ∀ n, B n →ᵇ ℝ := fun x n =>
    BoundedContinuousFunction.mkOfDiscrete (fun U => f n U x) 1
      (fun U V => Real.dist_le_of_mem_Icc_01 (hf n U x) (hf n V x))
  have hF : Continuous F := by
    apply continuous_pi
    intro n
    apply continuous_boundedCoordinates (f n) (hf n)
    apply (hl n).subset
    intro U x hx
    exact not_not.mp (fun h => hx ((hzero n U x).mpr h))
  have hi : IsInducing F := by
    apply isInducing_iff_nhds.mpr
    intro x
    refine le_antisymm (hF.continuousAt.le_comap) ?_
    apply hb.nhds_hasBasis.ge_iff.mpr
    rintro U ⟨hUB, hxU⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hUB
    let V : B n := ⟨U, hn⟩
    have hpos : 0 < f n V x := lt_of_le_of_ne (hf n V x).1
      (Ne.symm (fun h => ((hzero n V x).mp h) hxU))
    have hc : Continuous (fun z : (∀ n, B n →ᵇ ℝ) => z n V) :=
      (BoundedContinuousFunction.lipschitz_eval_const V).continuous.comp (continuous_apply n)
    have hn : {z : (∀ n, B n →ᵇ ℝ) | 0 < z n V} ∈ 𝓝 (F x) :=
      (isOpen_Ioi.preimage hc).mem_nhds hpos
    apply mem_of_superset (preimage_mem_comap hn)
    intro y hy
    have : f n V y ≠ 0 := ne_of_gt hy
    exact not_not.mp (fun h => this ((hzero n V y).mpr h))
  exact hi.pseudoMetrizableSpace

/-- The sufficiency direction of the full Nagata–Smirnov theorem. -/
theorem HasSigmaLocallyFiniteBasis.metrizableSpace [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) : MetrizableSpace X := by
  classical
  let : PerfectlyNormalSpace X := h.perfectlyNormalSpace
  obtain ⟨B, hl, hb⟩ := h
  have hex : ∀ n (U : B n), ∃ f : C(X, ℝ),
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, f x = 0 ↔ x ∉ (U : Set X)) := by
    intro n U
    obtain ⟨f, hf, hfr⟩ :=
      perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.mp
        (inferInstance : PerfectlyNormalSpace X) (U : Set X)ᶜ
        (hb.isOpen (mem_iUnion.mpr ⟨n, U.property⟩)).isClosed_compl
    refine ⟨f, hfr, ?_⟩
    intro x
    exact Iff.symm (show x ∈ (U : Set X)ᶜ ↔ f x = 0 by rw [hf]; rfl)
  choose f hf hz using hex
  let : PseudoMetrizableSpace X := pseudoMetrizable_of_cozero_basis B hl hb f hf hz
  infer_instance

/-- Full Nagata–Smirnov: a regular Hausdorff space is metrizable exactly when
it has an open basis which is a countable union of locally finite families. -/
theorem nagata_smirnov [T3Space X] :
    MetrizableSpace X ↔ HasSigmaLocallyFiniteBasis X := by
  constructor
  · intro h
    let := h
    exact exists_sigmaLocallyFiniteBasis (X := X)
  · exact HasSigmaLocallyFiniteBasis.metrizableSpace

/-- A compatible metric constructed from the basis criterion. Its topology is
definitionally the supplied topology, even when a layer is uncountable. -/
@[instance_reducible]
noncomputable def compatibleMetric [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) : MetricSpace X :=
  let : MetrizableSpace X := h.metrizableSpace
  metrizableSpaceMetric X

theorem compatibleMetric_topology [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) :
    (compatibleMetric h).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace X› := by
  with_reducible_and_instances rfl

/-- The full criterion with the sigma locally finite basis expanded explicitly. -/
theorem metrizable_iff_sigmaLocallyFiniteBasis [T3Space X] :
    MetrizableSpace X ↔ ∃ B : ℕ → Set (Set X),
      (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
        IsTopologicalBasis (⋃ n, B n) := nagata_smirnov

/-- The full criterion expressed by existence of an actual metric whose induced
topology equals the given topology. -/
theorem compatible_metric_iff [T3Space X] :
    (∃ m : MetricSpace X,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X›) ↔
      HasSigmaLocallyFiniteBasis X := by
  constructor
  · rintro ⟨m, hm⟩
    let : MetricSpace X := m.replaceTopology hm.symm
    exact exists_sigmaLocallyFiniteBasis (X := X)
  · intro h
    exact ⟨compatibleMetric h, compatibleMetric_topology h⟩

end NagataSmirnov
