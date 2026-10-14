/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Sequences
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Strict insertion from normality and countable paracompactness

A locally finite partition of unity subordinate to rational intermediate levels
gives a continuous weighted average between arbitrary semicontinuous bounds.
The sum is locally finite, so neither bound needs to be globally bounded.
-/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Normal countably paracompact spaces have strict insertion for all real
semicontinuous bounds. -/
theorem CountablyParacompact.strict_insertion [NormalSpace X]
    (hX : CountablyParacompact X) : StrictInsertion X := by
  classical
  intro h g hh hg hlt
  let U : ℚ → Set X := fun q => {x | h x < (q : ℝ) ∧ (q : ℝ) < g x}
  have ho : ∀ q, IsOpen (U q) := fun q =>
    (hh.isOpen_preimage (q : ℝ)).inter (hg.isOpen_preimage (q : ℝ))
  have hU : (⋃ q, U q) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨q, hq⟩ := exists_rat_btwn (hlt x)
    exact mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨V, hVo, hVU, hVf, hVUsub⟩ := hX.precise_refinement U ho hU
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ V hVo hVf (by rw [hVU])
  let f : X → ℝ := fun x => ∑ᶠ q : ℚ, ρ q x • (q : ℝ)
  refine ⟨f, ρ.continuous_finsum_smul (fun _ _ _ => continuousAt_const), ?_⟩
  intro x
  have hsum : ∑ q ∈ ρ.finsupport x, ρ q x = 1 := ρ.sum_finsupport (mem_univ x)
  have hf : f x = ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := by
    exact (ρ.sum_finsupport_smul_eq_finsum (fun q _ => (q : ℝ))).symm
  have hpos : ∀ q ∈ ρ.finsupport x, 0 < ρ q x := by
    intro q hq
    exact lt_of_le_of_ne (ρ.nonneg q x) (Ne.symm ((ρ.mem_finsupport x).mp hq))
  have hb : ∀ q ∈ ρ.finsupport x, h x < (q : ℝ) ∧ (q : ℝ) < g x := by
    intro q hq
    exact hVUsub q (hρ q (subset_closure ((ρ.mem_finsupport x).mp hq)))
  obtain ⟨q₀, hq₀⟩ := ρ.exists_pos (mem_univ x)
  have hq₀mem : q₀ ∈ ρ.finsupport x := (ρ.mem_finsupport x).mpr (ne_of_gt hq₀)
  constructor
  · calc
      h x = ∑ q ∈ ρ.finsupport x, ρ q x * h x := by rw [← Finset.sum_mul, hsum, one_mul]
      _ < ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := by
        apply Finset.sum_lt_sum
        · intro q hq
          exact (mul_lt_mul_of_pos_left (hb q hq).1 (hpos q hq)).le
        · exact ⟨q₀, hq₀mem, mul_lt_mul_of_pos_left (hb q₀ hq₀mem).1 hq₀⟩
      _ = f x := hf.symm
  · calc
      f x = ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := hf
      _ < ∑ q ∈ ρ.finsupport x, ρ q x * g x := by
        apply Finset.sum_lt_sum
        · intro q hq
          exact (mul_lt_mul_of_pos_left (hb q hq).2 (hpos q hq)).le
        · exact ⟨q₀, hq₀mem, mul_lt_mul_of_pos_left (hb q₀ hq₀mem).2 hq₀⟩
      _ = g x := by rw [← Finset.sum_mul, hsum, one_mul]

end Dowker
