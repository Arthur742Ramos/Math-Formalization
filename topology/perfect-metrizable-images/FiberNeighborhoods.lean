/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Maps.Basic

/-!
# Metric neighborhoods of compact fibers

A closed map sends the complement of a fiber-containing open set to a closed
set. Its complementary upper image is an open neighborhood of that fiber's
value. Compactness makes metric thickenings uniform around an entire fiber.
-/

@[expose] public section

open Set Function Metric

namespace PerfectImage

variable {X Y : Type*}

/-- The values whose entire fiber lies in `U`. -/
def upperImage (f : X → Y) (U : Set X) : Set Y := (f '' Uᶜ)ᶜ

theorem mem_upperImage_iff (f : X → Y) (U : Set X) (y : Y) :
    y ∈ upperImage f U ↔ f ⁻¹' {y} ⊆ U := by
  constructor
  · intro hy x hx
    by_contra hxU
    exact hy ⟨x, hxU, mem_singleton_iff.mp hx⟩
  · intro h hy
    obtain ⟨x, hxU, hxy⟩ := hy
    exact hxU (h (show x ∈ f ⁻¹' {y} from hxy))

theorem preimage_upperImage_subset (f : X → Y) (U : Set X) :
    f ⁻¹' upperImage f U ⊆ U := by
  intro x hx
  exact (mem_upperImage_iff f U (f x)).mp hx rfl

section Topological

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem upperImage_isOpen {f : X → Y} (hc : IsClosedMap f)
    {U : Set X} (hU : IsOpen U) : IsOpen (upperImage f U) :=
  (hc _ hU.isClosed_compl).isOpen_compl

end Topological

section Metric

variable [MetricSpace X]

/-- The values whose entire fiber lies within distance `r` of the fiber at `y`. -/
def fiberNeighborhood (f : X → Y) (r : ℝ) (y : Y) : Set Y :=
  upperImage f (thickening r (f ⁻¹' {y}))

theorem mem_fiberNeighborhood_iff (f : X → Y) (r : ℝ) (y z : Y) :
    z ∈ fiberNeighborhood f r y ↔ f ⁻¹' {z} ⊆ thickening r (f ⁻¹' {y}) :=
  mem_upperImage_iff f _ z

theorem fiberNeighborhood_isOpen [TopologicalSpace Y] {f : X → Y}
    (hc : IsClosedMap f) (r : ℝ) (y : Y) :
    IsOpen (fiberNeighborhood f r y) :=
  upperImage_isOpen hc isOpen_thickening

theorem mem_fiberNeighborhood_self (f : X → Y) {r : ℝ} (hr : 0 < r) (y : Y) :
    y ∈ fiberNeighborhood f r y :=
  (mem_fiberNeighborhood_iff f r y y).mpr (self_subset_thickening hr _)

/-- All sufficiently small fiber neighborhoods containing `y` are contained in
any prescribed open neighborhood of `y`. No separation assumption on the target
is needed for this estimate. -/
theorem exists_radius_star_subset [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f)
    (y : Y) {G : Set Y} (hG : IsOpen G) (hy : y ∈ G) :
    ∃ ε > (0 : ℝ), ∀ r, 0 < r → r < ε →
      ∀ z, y ∈ fiberNeighborhood f r z → fiberNeighborhood f r z ⊆ G := by
  have hFyG : f ⁻¹' {y} ⊆ f ⁻¹' G := by
    intro x hx
    change f x ∈ G
    rw [show f x = y from hx]
    exact hy
  obtain ⟨a, ha, hta⟩ := (hk y).exists_thickening_subset_open (hG.preimage hf) hFyG
  let V := fiberNeighborhood f (a / 2) y
  have hVo : IsOpen V := fiberNeighborhood_isOpen hc _ _
  have hyV : y ∈ V := mem_fiberNeighborhood_self f (half_pos ha) y
  have hFyV : f ⁻¹' {y} ⊆ f ⁻¹' V := by
    intro x hx
    change f x ∈ V
    rw [show f x = y from hx]
    exact hyV
  obtain ⟨δ, hδ, htδ⟩ := (hk y).exists_thickening_subset_open (hVo.preimage hf) hFyV
  refine ⟨min δ (a / 2), lt_min hδ (half_pos ha), ?_⟩
  intro r _hr hrε z hyz w hw
  have hrδ : r < δ := hrε.trans_le (min_le_left _ _)
  have hra : r < a / 2 := hrε.trans_le (min_le_right _ _)
  obtain ⟨x, hxy⟩ := hs y
  have hxF : x ∈ f ⁻¹' {y} := hxy
  obtain ⟨c, hcF, hxc⟩ := mem_thickening_iff.mp
    ((mem_fiberNeighborhood_iff f r z y).mp hyz hxF)
  have hcδ : c ∈ thickening δ (f ⁻¹' {y}) :=
    mem_thickening_iff.mpr ⟨x, hxF, by rw [dist_comm]; exact hxc.trans hrδ⟩
  have hzV : z ∈ V := by
    have hfc : f c ∈ V := htδ hcδ
    rw [show f c = z from hcF] at hfc
    exact hfc
  have hzTube : f ⁻¹' {z} ⊆ thickening (a / 2) (f ⁻¹' {y}) :=
    (mem_fiberNeighborhood_iff f (a / 2) y z).mp hzV
  obtain ⟨b, hbw⟩ := hs w
  have hbF : b ∈ f ⁻¹' {w} := hbw
  obtain ⟨d, hdF, hbd⟩ := mem_thickening_iff.mp
    ((mem_fiberNeighborhood_iff f r z w).mp hw hbF)
  obtain ⟨e, heF, hde⟩ := mem_thickening_iff.mp (hzTube hdF)
  have hbTube : b ∈ thickening a (f ⁻¹' {y}) := by
    apply mem_thickening_iff.mpr
    refine ⟨e, heF, ?_⟩
    calc
      dist b e ≤ dist b d + dist d e := dist_triangle _ _ _
      _ < r + a / 2 := add_lt_add hbd hde
      _ < a := (add_lt_add_of_lt_of_le hra le_rfl).trans_eq (add_halves a)
  have hfb : f b ∈ G := hta hbTube
  rw [hbw] at hfb
  exact hfb

end Metric
end PerfectImage
