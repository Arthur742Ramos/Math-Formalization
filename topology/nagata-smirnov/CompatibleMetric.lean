/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Compatible metric infrastructure for locally finite coordinate families

An arbitrary locally finite family of bounded continuous coordinates gives a
continuous map into a metric space of bounded functions with the uniform metric.
Only the layers, rather than their coordinate index types, will be countable.
-/

public section

open Set Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace NagataSmirnov

variable {X I : Type*} [TopologicalSpace X]

/-- Locally finite supports upgrade coordinatewise continuity to continuity
for the uniform metric on bounded functions. The index type is arbitrary. -/
theorem continuous_boundedCoordinates [TopologicalSpace I] [DiscreteTopology I]
    (f : I → C(X, ℝ)) (hf : ∀ i x, f i x ∈ Icc (0 : ℝ) 1)
    (hl : LocallyFinite (fun i => Function.support (f i))) :
    Continuous (fun x => BoundedContinuousFunction.mkOfDiscrete
      (fun i => f i x) 1
      (fun i j => Real.dist_le_of_mem_Icc_01 (hf i x) (hf j x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, hU, hfin⟩ := hl x
  have hc : ∀ᶠ y in 𝓝 x,
      ∀ i ∈ {i | (Function.support (f i) ∩ U).Nonempty},
        dist (f i y) (f i x) < ε / 2 := by
    apply (eventually_all_finite hfin).mpr
    intro i hi
    exact (f i).continuous.continuousAt.eventually
      (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hU, hc] with y hy hcy
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.dist_le (half_pos hε).le).mpr
  intro i
  by_cases hi : i ∈ {i | (Function.support (f i) ∩ U).Nonempty}
  · exact (hcy i hi).le
  · have hy0 : f i y = 0 := by
      by_contra h
      exact hi ⟨y, h, hy⟩
    have hx0 : f i x = 0 := by
      by_contra h
      exact hi ⟨x, h, mem_of_mem_nhds hU⟩
    simpa [hy0, hx0] using (half_pos hε).le

end NagataSmirnov
