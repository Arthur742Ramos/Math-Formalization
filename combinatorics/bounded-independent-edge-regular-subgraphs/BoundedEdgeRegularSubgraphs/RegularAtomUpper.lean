module

public import BoundedEdgeRegularSubgraphs.UpperRegularAtoms
public import BoundedEdgeRegularSubgraphs.OptimizedTilt
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# Degree variation in the upper atom estimate
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem degreeSum_one (i : α) :
    degreeSum (fun _ ↦ (1 : ℝ)) i = (Fintype.card α : ℝ) - 1 := by
  classical
  let u (j : α) : ℝ := if j = i then 1 else 0
  have hu : ∑ j, u j = 1 := by simp [u]
  have hs : ∑ j, (u j) ^ 2 = 1 := by simp [u, apply_ite (fun x : ℝ ↦ x ^ 2)]
  have heq : degreeSum (fun _ ↦ (1 : ℝ)) i =
      ∑ e : Edge α, (u e.val.1 + u e.val.2) ^ 2 := by
    unfold degreeSum
    refine Finset.sum_congr rfl (fun e _ ↦ ?_)
    have hne := ne_of_lt e.property
    by_cases h₁ : i = e.val.1
    · subst i
      simp [u, hne, hne.symm]
    · by_cases h₂ : i = e.val.2
      · subst i
        simp [u, hne, hne.symm]
      · simp [u, h₁, Ne.symm h₁, h₂, Ne.symm h₂]
  rw [heq, sum_edge_squares, hu, hs]
  ring

theorem degreeSum_probability_bounds (p : Edge α → Set.Icc (0 : ℝ) 1) (i : α) :
    degreeSum (fun e ↦ (p e : ℝ)) i ∈ Set.Icc 0 ((Fintype.card α : ℝ) - 1) := by
  classical
  constructor
  · unfold degreeSum
    exact Finset.sum_nonneg (fun e _ ↦ by split_ifs; exacts [(p e).property.1, le_rfl])
  · rw [← degreeSum_one (α := α) i]
    unfold degreeSum
    exact Finset.sum_le_sum (fun e _ ↦ by split_ifs; exacts [(p e).property.2, le_rfl])

private theorem varianceTilt_abs_le_ten (p : Edge α → Set.Icc (0 : ℝ) 1)
    (d : ℝ) (hd : d ∈ Set.Icc 0 ((Fintype.card α : ℝ) - 1))
    (hn : 3 ≤ Fintype.card α) (i : α) :
    |varianceTilt (degreeSum fun e ↦ (p e : ℝ)) d i| ≤ 10 := by
  let n : ℝ := Fintype.card α
  let μ := degreeSum fun e ↦ (p e : ℝ)
  have hn3 : 3 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have h₂ : 0 < n - 2 := by linarith
  have h₁ : 0 < n - 1 := by linarith
  have hg (j : α) : 0 ≤ μ j ∧ μ j ≤ n - 1 := degreeSum_probability_bounds p j
  have hmean₀ : 0 ≤ vertexMean μ := by
    unfold vertexMean
    exact div_nonneg (Finset.sum_nonneg fun j _ ↦ (hg j).1) hn0.le
  have hmean₁ : vertexMean μ ≤ n - 1 := by
    unfold vertexMean
    apply (div_le_iff₀ hn0).mpr
    change (∑ i, μ i) ≤ (n - 1) * n
    calc
      _ ≤ ∑ _ : α, (n - 1) := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ (hg j).2)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change n * (n - 1) = (n - 1) * n
        exact mul_comm _ _
  have ha : |μ i - vertexMean μ| ≤ n - 1 := by
    exact abs_le.mpr ⟨by linarith [(hg i).1], by linarith [(hg i).2]⟩
  have hb : |d - vertexMean μ| ≤ n - 1 := by
    exact abs_le.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hA : 4 / (n - 2) * |μ i - vertexMean μ| ≤ 8 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ h₂).mpr
    linarith
  have hB : 2 / (n - 1) * |d - vertexMean μ| ≤ 2 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ h₁).mpr (by linarith)
  change |-(4 / (n - 2)) * (μ i - vertexMean μ) +
    (2 / (n - 1)) * (d - vertexMean μ)| ≤ 10
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by norm_num) h₂.le),
    abs_of_nonneg (div_nonneg (by norm_num) h₁.le)]
  linarith

theorem exists_uniform_tilt_floor (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ (q : Set.Icc (0 : ℝ) 1) (s : ℝ), ξ ≤ (q : ℝ) → (q : ℝ) ≤ 1 - ξ →
        |s| ≤ 20 → δ ≤ (tiltProb q s : ℝ) ∧ (tiltProb q s : ℝ) ≤ 1 - δ := by
  let Z := 1 + Real.exp 20
  let δ := ξ * Real.exp (-20) / Z
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hδ : 0 < δ := div_pos (mul_pos hξ (Real.exp_pos _)) hZ
  have hE : Real.exp (-20) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  have hEZ : Real.exp (-20) ≤ Z := by dsimp [Z]; linarith [Real.exp_pos (20 : ℝ)]
  have hδle : δ ≤ ξ := (div_le_iff₀ hZ).mpr (mul_le_mul_of_nonneg_left hEZ hξ.le)
  refine ⟨δ, hδ, hδle.trans_lt hξ', ?_⟩
  intro q s hq₁ hq₂ hs
  let N := tiltNormalizer q s
  have hN : 0 < N := tiltNormalizer_pos _ _
  have hsmall : Real.exp (-20) ≤ Real.exp s := Real.exp_le_exp.mpr (abs_le.mp hs).1
  have hbig : Real.exp s ≤ Real.exp 20 := Real.exp_le_exp.mpr (abs_le.mp hs).2
  have hNZ : N ≤ Z := by
    have hprod : (q : ℝ) * Real.exp s ≤ Real.exp 20 :=
      (mul_le_mul_of_nonneg_right q.property.2 (Real.exp_nonneg _)).trans_eq (one_mul _)
        |>.trans hbig
    dsimp [N, Z, tiltNormalizer]
    linarith [q.property.1]
  have hnum : δ * N ≤ ξ * Real.exp (-20) := by
    calc
      _ ≤ δ * Z := mul_le_mul_of_nonneg_left hNZ hδ.le
      _ = _ := by dsimp only [δ]; exact div_mul_cancel₀ _ hZ.ne'
  constructor
  · change δ ≤ (q : ℝ) * Real.exp s / N
    apply (le_div_iff₀ hN).mpr
    exact hnum.trans (mul_le_mul hq₁ hsmall (Real.exp_nonneg _) q.property.1)
  · change (q : ℝ) * Real.exp s / N ≤ 1 - δ
    have hh : 1 - (q : ℝ) * Real.exp s / N = (1 - q : ℝ) / N := by
      field_simp [hN.ne']
      dsimp [N, tiltNormalizer]
      ring
    have hnumerator : ξ * Real.exp (-20) ≤ 1 - (q : ℝ) :=
      (mul_le_of_le_one_right hξ.le hE).trans (by linarith)
    have hh' : δ ≤ (1 - q : ℝ) / N := (le_div_iff₀ hN).mpr (hnum.trans hnumerator)
    linarith

/-- Proposition 8.1 for each prescribed common degree. -/
theorem probability_regular_degree_atom_le (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 3 ≤ n →
      ∀ (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1),
        (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ (d : ℕ), d < n →
      (graphLaw p).real (degreeAtom Finset.univ (fun _ ↦ (d : ℤ))) ≤
        (C / Real.sqrt n) ^ n *
          Real.exp (-2 * degreeVariation p / ((n : ℝ) - 2) -
            (n : ℝ) * ((d : ℝ) - vertexMean (degreeSum fun e ↦ (p e : ℝ))) ^ 2 /
              ((n : ℝ) - 1)) := by
  obtain ⟨δ, hδ, hδ', hfloor⟩ := exists_uniform_tilt_floor ξ hξ hξ'
  obtain ⟨C, hC, hbound⟩ := probability_degreeAtom_le_pow_inv_sqrt δ hδ hδ'
  refine ⟨C, hC, ?_⟩
  intro n hn p hp d hd
  let θ := varianceTilt (degreeSum fun e ↦ (p e : ℝ)) (d : ℝ)
  have hn' : 3 ≤ Fintype.card (Fin n) := by simpa
  have hd' : (d : ℝ) ∈ Set.Icc 0 ((Fintype.card (Fin n) : ℝ) - 1) := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h : (d : ℝ) + 1 ≤ n := by exact_mod_cast hd
    simp only [Fintype.card_fin]
    linarith
  have ht (i : Fin n) : |θ i| ≤ 10 := varianceTilt_abs_le_ten p d hd' hn' i
  have hp' (e : Edge (Fin n)) :
      δ ≤ (vertexTilt p θ e : ℝ) ∧ (vertexTilt p θ e : ℝ) ≤ 1 - δ := by
    apply hfloor (p e) _ (hp e).1 (hp e).2
    exact (abs_add_le _ _).trans (by linarith [ht e.val.1, ht e.val.2])
  have ha := probability_regular_degree_atom_le_variance_tilt p (d : ℤ) hn'
  simp only [Fintype.card_fin, Int.cast_natCast] at ha
  rw [mul_comm]
  exact ha.trans (mul_le_mul_of_nonneg_left
    (hbound n (by omega) (vertexTilt p θ) hp' (fun _ ↦ (d : ℤ))) (Real.exp_nonneg _))

end BoundedEdgeRegularSubgraphs
