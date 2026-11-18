module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

/-!
# A Gaussian sum uniform in the centre
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Every finite part of the translated integer Gaussian sum has a common bound. -/
theorem uniform_gaussian_sum :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (n : ℕ) (x : ℝ),
      (∑ d : Fin n, Real.exp (-((d.val : ℝ) - x) ^ 2)) ≤ K := by
  let g (z : ℤ) := Real.exp (-|(z : ℝ)|)
  have hs : Summable g := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> simpa [g, abs_of_nonneg, abs_neg] using Real.summable_exp_neg_nat
  refine ⟨max 1 (Real.exp 2 * ∑' z : ℤ, g z), le_max_left _ _, ?_⟩
  intro n x
  let a := Int.floor x
  let e : Fin n ↪ ℤ := ⟨fun d ↦ (d.val : ℤ) - a, by
    intro i j h
    apply Fin.ext
    dsimp at h
    omega⟩
  have ha : |x - (a : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    have h₁ : (a : ℝ) ≤ x := Int.floor_le x
    have h₂ : x < (a : ℝ) + 1 := Int.lt_floor_add_one x
    constructor <;> linarith
  have hpt (d : Fin n) :
      Real.exp (-((d.val : ℝ) - x) ^ 2) ≤ Real.exp 2 * g (e d) := by
    change Real.exp (-((d.val : ℝ) - x) ^ 2) ≤
      Real.exp 2 * Real.exp (-|(((d.val : ℤ) - a : ℤ) : ℝ)|)
    push_cast
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := abs_add_le ((d.val : ℝ) - x) (x - (a : ℝ))
    rw [show (d.val : ℝ) - x + (x - (a : ℝ)) = (d.val : ℝ) - (a : ℝ) by ring] at ht
    nlinarith only [ht, ha, sq_nonneg (|(d.val : ℝ) - x| - 1 / 2), sq_abs ((d.val : ℝ) - x)]
  calc
    _ ≤ ∑ d : Fin n, Real.exp 2 * g (e d) := Finset.sum_le_sum (fun d _ ↦ hpt d)
    _ = Real.exp 2 * ∑ z ∈ Finset.univ.map e, g z := by
      rw [Finset.mul_sum, Finset.sum_map]
    _ ≤ Real.exp 2 * (∑' z : ℤ, g z) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun _ _ ↦ Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ ≤ _ := le_max_right _ _

/-- A Gaussian sum on a finite integer interval, with explicit dependence on the rate. -/
theorem gaussian_sum_fin_le (n : ℕ) (v : Fin n) {b : ℝ} (hb : 0 < b) :
    (∑ i : Fin n, Real.exp (-b * ((i.val : ℝ) - (v.val : ℝ)) ^ 2)) ≤
      2 + Real.sqrt (Real.pi / b) := by
  classical
  let f (x : ℝ) := Real.exp (-b * x ^ 2)
  have hf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ f x := fun _ _ ↦ Real.exp_nonneg _
  have hanti : AntitoneOn f (Set.Ici (0 : ℝ)) := by
    intro x hx y _ hxy
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ((sq_le_sq₀ hx (hx.trans hxy)).mpr hxy) (neg_nonpos.mpr hb.le)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hsum := hanti.summable_of_integrableOn_Ioi_zero hint hf
  have hbound := hanti.tsum_le_integral hint hf
  change (∑' k : ℕ, f k) ≤ f 0 + ∫ x in Set.Ioi 0, f x at hbound
  have hfinite (S : Finset (Fin n)) (g : Fin n → ℕ) (hginj : Set.InjOn g (S : Set (Fin n)))
      (hd : ∀ i ∈ S, ((i.val : ℝ) - (v.val : ℝ)) ^ 2 = (g i : ℝ) ^ 2) :
      (∑ i ∈ S, Real.exp (-b * ((i.val : ℝ) - (v.val : ℝ)) ^ 2)) ≤
        f 0 + ∫ x in Set.Ioi 0, f x := by
    calc
      _ = ∑ i ∈ S, f (g i) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [f]
        rw [hd i hi]
      _ = ∑ k ∈ S.image g, f k := by rw [Finset.sum_image hginj]
      _ ≤ ∑' k : ℕ, f k := hsum.sum_le_tsum _ (fun _ _ ↦ Real.exp_nonneg _)
      _ ≤ _ := hbound
  let L : Finset (Fin n) := Finset.univ.filter (fun i ↦ i.val ≤ v.val)
  let U : Finset (Fin n) := Finset.univ.filter (fun i ↦ ¬ i.val ≤ v.val)
  have hL := hfinite L (fun i ↦ v.val - i.val) (by
    intro i hi j hj h
    have hi' : i.val ≤ v.val := (Finset.mem_filter.mp hi).2
    have hj' : j.val ≤ v.val := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    change v.val - i.val = v.val - j.val at h
    omega) (by
    intro i hi
    have h : i.val ≤ v.val := (Finset.mem_filter.mp hi).2
    rw [Nat.cast_sub h]
    ring)
  have hU := hfinite U (fun i ↦ i.val - v.val) (by
    intro i hi j hj h
    have hi' : ¬ i.val ≤ v.val := (Finset.mem_filter.mp hi).2
    have hj' : ¬ j.val ≤ v.val := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    change i.val - v.val = j.val - v.val at h
    omega) (by
    intro i hi
    have h : ¬ i.val ≤ v.val := (Finset.mem_filter.mp hi).2
    rw [Nat.cast_sub (by omega : v.val ≤ i.val)])
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun i ↦ i.val ≤ v.val) (fun i ↦ Real.exp (-b * ((i.val : ℝ) - v.val) ^ 2))
  have h := add_le_add hL hU
  change _ ≤ (f 0 + ∫ x in Set.Ioi 0, f x) + (f 0 + ∫ x in Set.Ioi 0, f x) at h
  rw [show f 0 = 1 by simp [f], show (∫ x in Set.Ioi 0, f x) =
    Real.sqrt (Real.pi / b) / 2 by simpa [f] using integral_gaussian_Ioi b] at h
  change (∑ i ∈ L, Real.exp (-b * ((i.val : ℝ) - v.val) ^ 2)) +
    (∑ i ∈ U, Real.exp (-b * ((i.val : ℝ) - v.val) ^ 2)) = _ at hsplit
  rw [hsplit] at h
  linarith


end BoundedEdgeRegularSubgraphs
