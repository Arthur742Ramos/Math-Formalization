module

public import BoundedEdgeRegularSubgraphs.RegularAtomUpper
import BoundedEdgeRegularSubgraphs.GaussianSum
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# Summing the upper atom estimates over the common degree
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem probability_regular_le_sum_degree_atoms
    {n : ℕ} (hn : 0 < n) (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1) :
    (graphLaw p).real regularEvent ≤
      ∑ d : Fin n, (graphLaw p).real (degreeAtom Finset.univ (fun _ ↦ (d.val : ℤ))) := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  have hu : regularEvent =ᵐ[graphLaw p]
      (⋃ d : Fin n, degreeAtom Finset.univ (fun _ ↦ (d.val : ℤ))) := by
    filter_upwards [graphLaw_ae_binary p] with w hw
    apply propext
    change w ∈ regularEvent ↔ w ∈ ⋃ d : Fin n, degreeAtom Finset.univ (fun _ ↦ (d.val : ℤ))
    rw [Set.mem_iUnion]
    constructor
    · intro he
      let q (e : Edge (Fin n)) : Set.Icc (0 : ℝ) 1 := ⟨w e, by
        rcases hw e with h | h <;> simp [h]⟩
      let D := degreeVector Finset.univ w
      have hbridge (i : Fin n) : (D i : ℝ) = degreeSum w i :=
        degreeVector_univ_eq_degreeSum w hw i
      have hrow : (D i₀ : ℝ) ∈ Set.Icc 0 ((n : ℝ) - 1) := by
        rw [hbridge]
        simpa only [Fintype.card_fin] using degreeSum_probability_bounds q i₀
      have hd₀ : 0 ≤ D i₀ := by exact_mod_cast hrow.1
      let d := (D i₀).toNat
      have hd : (d : ℤ) = D i₀ := Int.toNat_of_nonneg hd₀
      have hlt : (d : ℝ) < n := by
        have : (d : ℝ) = (D i₀ : ℝ) := by exact_mod_cast hd
        linarith [hrow.2]
      refine ⟨⟨d, by exact_mod_cast hlt⟩, ?_⟩
      change D = fun _ ↦ (d : ℤ)
      funext i
      rw [hd]
      have hh : (D i : ℝ) = (D i₀ : ℝ) := by
        rw [hbridge, hbridge]
        exact (show ∀ i j, degreeSum w i = degreeSum w j from he) i i₀
      exact_mod_cast hh
    · rintro ⟨d, hd⟩
      have h : degreeVector Finset.univ w = fun _ ↦ (d.val : ℤ) := hd
      change ∀ i j, degreeSum w i = degreeSum w j
      intro i j
      rw [← degreeVector_univ_eq_degreeSum w hw, ← degreeVector_univ_eq_degreeSum w hw, h]
  rw [measureReal_congr hu]
  exact measureReal_iUnion_fintype_le _

/-- The regularity bound after summing over the common degree in Proposition 8.1. -/
theorem probability_regular_le_variation_gaussian (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 3 ≤ n →
      ∀ (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) →
      (graphLaw p).real regularEvent ≤
        (C / Real.sqrt n) ^ n * Real.exp (-2 * degreeVariation p / ((n : ℝ) - 2)) := by
  obtain ⟨C, hC, hpoint⟩ := probability_regular_degree_atom_le ξ hξ hξ'
  obtain ⟨K, hK, hsum⟩ := uniform_gaussian_sum
  have hKpos : 0 < K := by linarith
  refine ⟨C * K, mul_pos hC hKpos, ?_⟩
  intro n hn p hp
  let x := vertexMean (degreeSum fun e ↦ (p e : ℝ))
  let a := -2 * degreeVariation p / ((n : ℝ) - 2)
  let R := (C / Real.sqrt n) ^ n
  have hR : 0 ≤ R := pow_nonneg (div_nonneg hC.le (Real.sqrt_nonneg _)) _
  have hR' : R * K ≤ ((C * K) / Real.sqrt n) ^ n := by
    have hKpow : K ≤ K ^ n := by
      simpa using pow_le_pow_right₀ hK (show 1 ≤ n by omega)
    calc
      _ ≤ R * K ^ n := mul_le_mul_of_nonneg_left hKpow hR
      _ = _ := by rw [← mul_pow, div_mul_eq_mul_div]
  have hpt (d : Fin n) :
      (graphLaw p).real (degreeAtom Finset.univ (fun _ ↦ (d.val : ℤ))) ≤
        (R * Real.exp a) * Real.exp (-((d.val : ℝ) - x) ^ 2) := by
    have h := hpoint n hn p hp d.val d.isLt
    change _ ≤ R * Real.exp (a - (n : ℝ) * ((d.val : ℝ) - x) ^ 2 / ((n : ℝ) - 1)) at h
    rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (mul_nonneg hR (Real.exp_nonneg _)))
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoef : 0 < (n : ℝ) - 1 := by linarith
    apply neg_le_neg
    apply (le_div_iff₀ hcoef).mpr
    nlinarith [sq_nonneg ((d.val : ℝ) - x)]
  calc
    _ ≤ ∑ d : Fin n, (graphLaw p).real (degreeAtom Finset.univ (fun _ ↦ (d.val : ℤ))) :=
      probability_regular_le_sum_degree_atoms (by omega) p
    _ ≤ ∑ d : Fin n, (R * Real.exp a) * Real.exp (-((d.val : ℝ) - x) ^ 2) :=
      Finset.sum_le_sum (fun d _ ↦ hpt d)
    _ ≤ (R * Real.exp a) * K := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum n x) (mul_nonneg hR (Real.exp_nonneg _))
    _ = (R * K) * Real.exp a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hR' (Real.exp_nonneg _)

end BoundedEdgeRegularSubgraphs
