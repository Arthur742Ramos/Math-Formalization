/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

import PerfectImage

open Set Function Topology TopologicalSpace

universe u v

-- Upper images deliberately contain values outside the range. Surjectivity
-- belongs to the preservation theorem, not to either selected definition.
example : PerfectImage.upperImage (fun _ : Empty => ()) ∅ = Set.univ := by
  ext y
  simp [PerfectImage.upperImage]

-- The preservation result permits the empty domain and codomain.
example : MetrizableSpace Empty :=
  PerfectImage.metrizable_image_of_proper isProperMap_id Function.surjective_id

-- Product projections can have arbitrary infinite compact fibers. The target
-- carries no metrizability or separation premise in this specialization.
example {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [CompactSpace K] [Nonempty K] [MetrizableSpace (K × Y)] : MetrizableSpace Y := by
  apply PerfectImage.metrizable_image_of_proper (f := (Prod.snd : K × Y → Y))
    isProperMap_snd_of_compactSpace
  intro y
  exact ⟨(Classical.choice inferInstance, y), rfl⟩

-- For an identity map, fiber neighborhoods recover ordinary metric balls.
example {X : Type u} [MetricSpace X] (r : ℝ) (x : X) :
    PerfectImage.fiberNeighborhood (id : X → X) r x = Metric.ball x r := by
  simp [PerfectImage.fiberNeighborhood, PerfectImage.upperImage]

-- The concrete conclusion preserves the supplied codomain topology.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [MetrizableSpace X] {f : X → Y} (h : IsProperMap f) (hs : Surjective f) :
    ∃ m : MetricSpace Y, m.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Y) :=
  PerfectImage.exists_compatibleMetric h.continuous h.isClosedMap
    (fun _ => h.isCompact_preimage isCompact_singleton) hs
