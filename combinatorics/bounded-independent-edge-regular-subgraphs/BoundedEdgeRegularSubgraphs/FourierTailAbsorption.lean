module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Combining the two tail estimates in Lemma B.1
-/

public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- Control of the two tail regions in terms of total mass gives their
bound in terms of the mass near the modes. -/
theorem fourier_tail_absorption {J P T N scale A a b C : ℝ}
    (hJ : J ≤ P + T + N) (hP : P ≤ C * scale)
    (hT : T ≤ A + a * J) (hN : N ≤ b * J)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1 / 2) (hJ₀ : 0 ≤ J) :
    T + N ≤ A + 2 * (a + b) * (C * scale + A) := by
  have h₁ : J ≤ C * scale + A + (a + b) * J := by
    linarith only [hJ, hP, hT, hN]
  have h₂ : J ≤ 2 * (C * scale + A) := by
    have h := mul_le_mul_of_nonneg_right hab hJ₀
    linarith only [h, h₁]
  have h₃ := mul_le_mul_of_nonneg_left h₂ (add_nonneg ha hb)
  linarith only [hT, hN, h₃]

/-- If the normalized many-bad-edge contribution and the two relative
tail rates vanish, the normalized combined tail vanishes. -/
theorem tendsto_fourier_tail_of_absorption {ι : Type*} {l : Filter ι}
    (J P T N scale A a b : ι → ℝ) (C : ℝ)
    (hA : Tendsto (fun k ↦ A k / scale k) l (𝓝 0))
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 0))
    (h : ∀ᶠ k in l, 0 < scale k ∧ 0 ≤ J k ∧ 0 ≤ T k ∧ 0 ≤ N k ∧
      0 ≤ a k ∧ 0 ≤ b k ∧ a k + b k ≤ 1 / 2 ∧
      J k ≤ P k + T k + N k ∧ P k ≤ C * scale k ∧
      T k ≤ A k + a k * J k ∧ N k ≤ b k * J k) :
    Tendsto (fun k ↦ (T k + N k) / scale k) l (𝓝 0) := by
  have hi : Tendsto (fun k ↦ A k / scale k + 2 * (a k + b k) * (C + A k / scale k)) l (𝓝 0) := by
    simpa only [add_zero, mul_zero, zero_mul] using
      hA.add ((tendsto_const_nhds.mul (ha.add hb)).mul (tendsto_const_nhds.add hA))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi ?_ ?_
  · filter_upwards [h] with k hk
    exact div_nonneg (add_nonneg hk.2.2.1 hk.2.2.2.1) hk.1.le
  · filter_upwards [h] with k hk
    obtain ⟨hs, hJ, hT, hN, ha', hb', hab, hsplit, hP, hTa, hNb⟩ := hk
    have hs' := fourier_tail_absorption hsplit hP hTa hNb ha' hb' hab hJ
    apply (div_le_iff₀ hs).2
    convert hs' using 1
    field_simp

end BoundedEdgeRegularSubgraphs
