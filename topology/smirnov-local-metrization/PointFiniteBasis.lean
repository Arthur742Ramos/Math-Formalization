/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import Metrization
public import Mathlib.Topology.Compactness.Paracompact

/-!
# A sigma locally finite basis from a point finite metrizable cover

Refine the cover of all local metric balls at each reciprocal natural radius.
At a fixed point, only finitely many patches contain it, so a common radius
works in all these patches. The triangle inequality controls any refining set
that contains the point.

Reference: James R. Munkres, *Topology*, second edition, Section 42,
Theorem 42.1, pages 261–262.
-/

public section

open Set TopologicalSpace Metric

namespace Smirnov

variable {X I : Type*} [TopologicalSpace X]

/-- A paracompact space with a point finite open cover by metrizable patches
admits a sigma locally finite basis. Neither the cover nor a basis layer is
required to be countable. -/
theorem exists_sigmaLocallyFiniteBasis_of_pointFinite_open_cover [ParacompactSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hpf : ∀ x, {i | x ∈ U i}.Finite) (hmet : ∀ i, MetrizableSpace (U i)) :
    NagataSmirnov.HasSigmaLocallyFiniteBasis X := by
  classical
  let : ∀ i, MetrizableSpace (U i) := hmet
  let : ∀ i, MetricSpace (U i) := fun i => metrizableSpaceMetric (U i)
  let r (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
  have hr : ∀ n, 0 < r n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  let C (n : ℕ) (p : Σ i, U i) : Set X := Subtype.val '' ball p.2 (r n)
  have hCo : ∀ n p, IsOpen (C n p) := fun n p =>
    (hU p.1).isOpenMap_subtype_val _ isOpen_ball
  have hCc : ∀ n, ⋃ p, C n p = univ := by
    intro n
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨i, hxi⟩ := iUnion_eq_univ_iff.mp hcover x
    exact ⟨⟨i, ⟨x, hxi⟩⟩, ⟨⟨x, hxi⟩, mem_ball_self (hr n), rfl⟩⟩
  choose D hDo hDc hDf hDsub using fun n => precise_refinement (C n) (hCo n) (hCc n)
  refine ⟨fun n => range (D n), fun n => (hDf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro W hW
    obtain ⟨n, p, rfl⟩ := mem_iUnion.mp hW
    exact hDo n p
  · intro x G hxG hG
    let S : Set I := {i | x ∈ U i}
    have hS : S.Finite := hpf x
    let : Fintype S := hS.fintype
    have hball : ∀ i : S, ∃ δ > (0 : ℝ),
        ball (⟨x, i.2⟩ : U i.1) δ ⊆ Subtype.val ⁻¹' G := by
      intro i
      exact Metric.isOpen_iff.mp (hG.preimage continuous_subtype_val) _ hxG
    choose δ hδ hδsub using hball
    choose k hk using fun i : S => exists_nat_one_div_lt (half_pos (hδ i))
    obtain ⟨n, hn⟩ := (finite_range k).bddAbove
    have hnrad : ∀ i : S, r n < δ i / 2 := by
      intro i
      have hkn : k i ≤ n := hn (mem_range_self i)
      have hrad : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (k i + 1 : ℝ) :=
        one_div_le_one_div_of_le (Nat.cast_add_one_pos (k i))
          (by exact_mod_cast Nat.add_le_add_right hkn 1)
      exact hrad.trans_lt (hk i)
    obtain ⟨p, hxp⟩ := iUnion_eq_univ_iff.mp (hDc n) x
    obtain ⟨z, hzc, hzx⟩ := hDsub n p hxp
    have hxi : x ∈ U p.1 := hzx ▸ z.2
    have hzEq : z = (⟨x, hxi⟩ : U p.1) := Subtype.ext hzx
    rw [hzEq] at hzc
    let ix : S := ⟨p.1, hxi⟩
    refine ⟨D n p, mem_iUnion_of_mem n (mem_range_self p), hxp, ?_⟩
    intro y hy
    obtain ⟨w, hwc, rfl⟩ := hDsub n p hy
    apply hδsub ix
    rw [mem_ball] at hwc hzc ⊢
    calc
      dist w (⟨x, hxi⟩ : U p.1) ≤ dist w p.2 + dist p.2 ⟨x, hxi⟩ :=
        dist_triangle _ _ _
      _ = dist w p.2 + dist (⟨x, hxi⟩ : U p.1) p.2 := by rw [dist_comm p.2]
      _ < r n + r n := add_lt_add hwc hzc
      _ < δ ix := (add_lt_add (hnrad ix) (hnrad ix)).trans_eq (add_halves (δ ix))

end Smirnov
