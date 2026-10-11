/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Sequences
public import Thresholds

/-!
# Normality and countable paracompactness from strict insertion

Closed-set indicators recover normality. The reciprocal of the first index
outside a decreasing closed sequence is positive and lower semicontinuous;
inserting a positive continuous minorant recovers the closed-sequence property.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

theorem StrictInsertion.normal_space (hI : StrictInsertion X) : NormalSpace X := by
  classical
  constructor
  intro A B hA hB hd
  let h : X → ℝ := A.indicator (fun _ => 1)
  let g : X → ℝ := fun x => 2 + B.indicator (fun _ => (-1 : ℝ)) x
  have hh : UpperSemicontinuous h := hA.upperSemicontinuous_indicator (by norm_num)
  have hg : LowerSemicontinuous g :=
    continuous_const.lowerSemicontinuous.add (hB.lowerSemicontinuous_indicator (by norm_num))
  have hlt : ∀ x, h x < g x := by
    intro x
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := fun hxB => Set.disjoint_left.mp hd hxA hxB
      norm_num [h, g, hxA, hxB]
    · by_cases hxB : x ∈ B <;> norm_num [h, g, hxA, hxB]
  obtain ⟨f, hf, hb⟩ := hI h g hh hg hlt
  refine ⟨{x | 1 < f x}, {x | f x < 1}, isOpen_lt continuous_const hf,
    isOpen_lt hf continuous_const, ?_, ?_, ?_⟩
  · intro x hx
    simpa [h, hx] using (hb x).1
  · intro x hx
    have hxg : g x = 1 := by norm_num [g, hx]
    change f x < 1
    rw [← hxg]
    exact (hb x).2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    change (1 : ℝ) < f x at hx
    change f x < 1 at hy
    exact (not_lt_of_gt hx) hy

theorem StrictInsertion.closed_sequence_property (hI : StrictInsertion X) :
    ClosedSequenceProperty X := by
  classical
  intro F hFc hFa hFe
  have he : ∀ x : X, ∃ n, x ∉ F n := by
    intro x
    by_contra! hx
    have hmem : x ∈ ⋂ n, F n := mem_iInter.mpr hx
    rw [hFe] at hmem
    exact hmem
  let escape : X → ℕ := fun x => Nat.find (he x)
  let g : X → ℝ := fun x => threshold (escape x)
  have hg : LowerSemicontinuous g := by
    intro x a ha
    have hx : x ∈ (F (escape x))ᶜ := Nat.find_spec (he x)
    filter_upwards [(hFc (escape x)).isOpen_compl.mem_nhds hx] with y hy
    have hyfind : escape y ≤ escape x := Nat.find_min' (he y) hy
    exact ha.trans_le (threshold_antitone hyfind)
  obtain ⟨f, hf, hfg⟩ := hI (fun _ => 0) g continuous_const.upperSemicontinuous hg
    (fun x => threshold_pos (escape x))
  refine ⟨fun n => {x | f x < threshold n},
    (fun _ => isOpen_lt hf continuous_const), ?_, ?_⟩
  · intro n x hx
    have hn : n ≤ escape x := by
      by_contra! hn
      exact Nat.find_spec (he x) (hFa hn.le hx)
    exact (hfg x).2.trans_le (threshold_antitone hn)
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_threshold_lt (hfg x).1
    exact hn.not_gt (mem_iInter.mp hx n)

theorem StrictInsertion.countably_paracompact (hI : StrictInsertion X) :
    CountablyParacompact X := by
  let := hI.normal_space
  exact countablyParacompact_of_closed_sequence_property hI.closed_sequence_property

end Dowker
