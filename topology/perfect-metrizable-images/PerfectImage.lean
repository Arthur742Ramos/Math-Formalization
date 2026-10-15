/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import FiberNeighborhoods
public import PerfectParacompactSupport
public import NagataSmirnovSupport.Metrization

/-!
# Perfect images of metrizable spaces

Perfect continuous surjections preserve ordinary metrizability without any
countability assumption. Compact-fiber metric neighborhoods supply shrinking
open covers, whose locally finite refinements form a sigma locally finite basis.

Reference: K. Sakai, *Geometric Aspects of General Topology*, second-edition
author manuscript (November 2, 2023), Proposition 2.4.5(1), pp. 50–51.
The previously registered perfect-map and Nagata–Smirnov results are reused.
-/

@[expose] public section

open Set Function TopologicalSpace Topology Metric

namespace PerfectImage

universe uImage vImage
variable {X : Type uImage} {Y : Type vImage} [TopologicalSpace X] [TopologicalSpace Y]

/-- Locally finite refinements of the compact-fiber metric neighborhood covers
form a basis. The target needs only paracompactness at this construction stage. -/
theorem sigmaLocallyFiniteBasis_image [MetrizableSpace X] [ParacompactSpace Y]
    {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    NagataSmirnov.HasSigmaLocallyFiniteBasis Y := by
  classical
  let : MetricSpace X := metrizableSpaceMetric X
  have hr : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ) := fun n =>
    div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hcover : ∀ n : ℕ, ⋃ y : Y, fiberNeighborhood f (1 / (n + 1 : ℝ)) y = univ := by
    intro n
    exact iUnion_eq_univ_iff.mpr fun y => ⟨y, mem_fiberNeighborhood_self f (hr n) y⟩
  choose V hVo hVc hVf hVs using fun n : ℕ =>
    precise_refinement (fiberNeighborhood f (1 / (n + 1 : ℝ)))
      (fiberNeighborhood_isOpen hc _) (hcover n)
  refine ⟨fun n => range (V n), fun n => (hVf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    rcases mem_iUnion.mp hU with ⟨n, y, rfl⟩
    exact hVo n y
  · intro y G hy hG
    obtain ⟨ε, hε, hεG⟩ := exists_radius_star_subset hf hc hk hs y hG hy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨z, hyz⟩ := iUnion_eq_univ_iff.mp (hVc n) y
    exact ⟨V n z, mem_iUnion.mpr ⟨n, mem_range_self z⟩, hyz,
      (hVs n z).trans (hεG _ (hr n) hn z (hVs n z hyz))⟩

/-- A continuous closed surjection with compact fibers from an arbitrary
metrizable space has a metrizable codomain. Target separation is derived. -/
theorem metrizable_image [MetrizableSpace X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    MetrizableSpace Y := by
  let : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨hP, hT⟩ := PerfectParacompact.paracompact_t2_image hf hc hk hs
  let : ParacompactSpace Y := hP
  let : T2Space Y := hT
  let : NormalSpace Y := PerfectParacompact.normal_image hf hc hs
  let : T3Space Y := inferInstance
  exact (sigmaLocallyFiniteBasis_image hf hc hk hs).metrizableSpace

/-- The same perfect-image theorem with Mathlib's proper-map interface. -/
theorem metrizable_image_of_proper [MetrizableSpace X] {f : X → Y}
    (hf : IsProperMap f) (hs : Surjective f) : MetrizableSpace Y :=
  metrizable_image hf.continuous hf.isClosedMap
    (fun _ => hf.isCompact_preimage isCompact_singleton) hs

/-- An actual metric inducing the codomain's original topology. -/
@[instance_reducible]
noncomputable def compatibleMetric [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) : MetricSpace Y := by
  let : MetrizableSpace Y := metrizable_image hf hc hk hs
  exact metrizableSpaceMetric Y

theorem compatibleMetric_topology [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) :
    (compatibleMetric hf hc hk hs).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Y) := by
  with_reducible_and_instances rfl

/-- The conclusion expressed without the `MetrizableSpace` class. -/
theorem exists_compatibleMetric [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) :
    ∃ m : MetricSpace Y, m.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Y) :=
  ⟨compatibleMetric hf hc hk hs, compatibleMetric_topology hf hc hk hs⟩

end PerfectImage
