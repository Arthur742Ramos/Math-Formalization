module

public import BoundedEdgeRegularSubgraphs.LargeCellScale
public import BoundedEdgeRegularSubgraphs.NearBalancedBlockPacking
public import BoundedEdgeRegularSubgraphs.BlockRegularAmplification
public import BoundedEdgeRegularSubgraphs.InducedDegreeTargets
public import BoundedEdgeRegularSubgraphs.CellRowBalance
import Mathlib.Tactic

/-!
# Amplification from the large-cell hypothesis
-/

@[expose] public section

open Set Function Filter MeasureTheory

namespace BoundedEdgeRegularSubgraphs

/-- The large-cell condition (6.1), stated with the normalized
expected degrees on each induced array. -/
noncomputable def HasLargeBalancedCells {n : ℕ} (s c₀ C₀ : ℝ)
    (p : Edge (Fin n) → Icc (0 : ℝ) 1) : Prop :=
  ∀ (R : Finset (Fin n)) (h : ℝ), 0 < h → h ≤ 1 → 2 ≤ c₀ * (R.card : ℝ) * h ^ s →
    ∃ U ⊆ R, c₀ * (R.card : ℝ) * h ^ s ≤ U.card ∧
      ∀ i : U, |degreeSum (fun e ↦ (induce U p e).val) i / ((U.card : ℝ) - 1) -
        arrayDensity (induce U p)| ≤ C₀ * h

private theorem sampleRowMean_eq_induced_degree {n : ℕ} (p : Edge (Fin n) → Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (hS : 1 ≤ S.card) (i : S) :
    sampleRowMean S (symmetricEdgeWeight (fun e ↦ (p e : ℝ))) i.val =
      degreeSum (fun e ↦ (induce S p e).val) i / ((S.card : ℝ) - 1) := by
  unfold sampleRowMean
  rw [Nat.cast_sub hS, Nat.cast_one]
  congr 1
  exact (degreeSum_induce_eq_sum_erase S (fun e ↦ (p e : ℝ)) i).symm

/-- Theorem 6.1 follows quantitatively from the near-balanced block
success bound of Theorem 4.1. -/
theorem exactOrder_failure_le_of_largeBalancedCells_and_block_success {s c₀ C₀ ξ H p₀ : ℝ}
    (hs : 0 ≤ s) (hc₀ : 0 < c₀) (hH : 1 ≤ H) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hSuccess : ∀ᶠ k : ℕ in atTop, ∀ {β : Type} [Fintype β] [LinearOrder β],
      Fintype.card β = regularBlockSize H k →
      ∀ q : Edge β → Icc (0 : ℝ) 1, (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
        (∃ p ∈ Icc ξ (1 - ξ), ∀ i, |degreeSum (fun e ↦ (q e : ℝ)) i /
          ((Fintype.card β : ℝ) - 1) - p| ≤ (C₀ + 1) * (Real.sqrt k)⁻¹) →
        p₀ ≤ (graphLaw q).real (exactOrderEvent k)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ (n : ℕ),
      (k : ℝ) ≤ a * (n : ℝ) ^ (2 / (s + 3)) →
      ∀ p : Edge (Fin n) → Icc (0 : ℝ) 1, (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) →
        HasLargeBalancedCells s c₀ C₀ p →
        (graphLaw p).real (exactOrderEvent k)ᶜ ≤ Real.exp (-c * (n : ℝ) / ((k : ℝ) * Real.sqrt k)) := by
  obtain ⟨a, ha, hScale⟩ := exists_largeCell_blockScale hs hc₀ hH
  let c := p₀ / (4 * H)
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨a, c, ha, hc, ?_⟩
  filter_upwards [hSuccess, hScale, eventually_regularBlockSize_bounds hH,
    eventually_ge_atTop (1 : ℕ)] with k hSuccess' hScale' hBlock hk
  intro n hOrder p hp hCells
  let m := regularBlockSize H k
  let h := (Real.sqrt k)⁻¹
  let w := symmetricEdgeWeight (fun e ↦ (p e : ℝ))
  let U : Finset (Fin n) := Finset.univ
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h₀ : 0 < h := inv_pos.mpr (Real.sqrt_pos.mpr hk₀)
  have h₁ : h ≤ 1 := by
    have hS : (1 : ℝ) ≤ Real.sqrt k := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ k by exact_mod_cast hk)
    simpa only [inv_one] using inv_anti₀ zero_lt_one hS
  have hW (i : Fin n) (_ : i ∈ U) (j : Fin n) (hj : j ∈ U.erase i) :
      w i j ∈ Icc (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1.symm with hl | hl
    · rw [show w i j = (p ⟨(i, j), hl⟩ : ℝ) from symmetricEdgeWeight_eq_of_lt _ hl]
      exact (p _).property
    · rw [show w i j = (p ⟨(j, i), hl⟩ : ℝ) from symmetricEdgeWeight_eq_of_gt _ hl]
      exact (p _).property
  have extract (R : Finset (Fin n)) (_ : R ⊆ U) (hSize : U.card ≤ 2 * R.card) :
      ∃ T ⊆ R, m ≤ T.card ∧ ∃ p' ∈ Icc ξ (1 - ξ),
        ∀ i ∈ T, |sampleRowMean T w i - p'| ≤ C₀ * h := by
    have hScaleR : (m : ℝ) ≤ c₀ * (R.card : ℝ) * h ^ s :=
      hScale' n R.card hOrder (by simpa only [U, Finset.card_univ, Fintype.card_fin] using hSize)
    have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hBlock.1
    obtain ⟨T, hTR, hT, hBal⟩ := hCells R h h₀ h₁ (hm₂.trans hScaleR)
    have hmT : m ≤ T.card := by exact_mod_cast hScaleR.trans hT
    have hT₂ : 2 ≤ Fintype.card T := by rw [Fintype.card_coe]; omega
    have hD := (row_density_mem_Icc (induce T p) hT₂ (fun e ↦ (hp (inducedEdge T e)).1)
      (fun e ↦ (hp (inducedEdge T e)).2)).1
    refine ⟨T, hTR, hmT, arrayDensity (induce T p), hD, fun i hi ↦ ?_⟩
    rw [sampleRowMean_eq_induced_degree p T (by omega) ⟨i, hi⟩]
    exact hBal ⟨i, hi⟩
  obtain ⟨B, hB, hDis, hCover⟩ := exists_disjoint_nearBalanced_block_packing U w hBlock.1 h₀.le hW
    hBlock.2.2.2 (ξ := ξ) (a := C₀ * h) extract
  have hS (T : B) : p₀ ≤ (graphLaw (induce T.val p)).real (exactOrderEvent k) := by
    obtain ⟨_, hTm, p', hp', he⟩ := hB T.val T.property
    apply hSuccess' ((Fintype.card_coe T.val).trans hTm) (induce T.val p)
      (fun e ↦ hp (inducedEdge T.val e))
    refine ⟨p', hp', ?_⟩
    intro i
    have hT : 1 ≤ T.val.card := by rw [hTm]; omega
    have hi := he i.val i.property
    rw [sampleRowMean_eq_induced_degree p T.val hT i] at hi
    rw [Fintype.card_coe]
    exact hi.trans_eq (by ring)
  have hprob := probability_exactOrder_failure_le_of_disjoint_blocks p (fun T : B ↦ T.val)
    (fun T V hne ↦ hDis T.property V.property (fun h ↦ hne (Subtype.ext h)))
    k hp₀.le hp₁ hS
  rw [Fintype.card_coe] at hprob
  refine hprob.trans (Real.exp_le_exp.mpr ?_)
  have hCov : (n : ℝ) ≤ 2 * (B.card : ℝ) * (m : ℝ) := by
    have h := hCover.le
    simp only [U, Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast (by simpa only [Nat.mul_assoc] using h : n ≤ 2 * B.card * m)
  have hCov' := hCov.trans (mul_le_mul_of_nonneg_left hBlock.2.2.1
    (show 0 ≤ 2 * (B.card : ℝ) by positivity))
  have hScale : (n : ℝ) / (4 * H * ((k : ℝ) * Real.sqrt k)) ≤ (B.card : ℝ) := by
    apply (div_le_iff₀ (show 0 < 4 * H * ((k : ℝ) * Real.sqrt k) by positivity)).2
    linarith only [hCov']
  have h := mul_le_mul_of_nonneg_left hScale hp₀.le
  rw [show p₀ * ((n : ℝ) / (4 * H * ((k : ℝ) * Real.sqrt k))) =
    c * (n : ℝ) / ((k : ℝ) * Real.sqrt k) by dsimp only [c]; ring] at h
  simpa only [neg_mul, neg_div] using neg_le_neg h

end BoundedEdgeRegularSubgraphs
