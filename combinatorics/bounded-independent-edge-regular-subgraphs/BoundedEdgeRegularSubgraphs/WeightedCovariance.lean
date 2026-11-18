module

public import BoundedEdgeRegularSubgraphs.OverlapInverse
import Mathlib.Tactic

/-!
# Covariance bounds for arbitrary bounded positive edge weights
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The sum of weighted outer products of edge incidence vectors. -/
noncomputable def weightedDegreeMatrix (A : Finset (Edge α)) (w : Edge α → ℝ) : Matrix α α ℝ :=
  fun i j ↦ ∑ e ∈ A, w e * (edgeIncidence e i : ℝ) * (edgeIncidence e j : ℝ)

private noncomputable def probabilityOfVariance (v : Set.Icc (0 : ℝ) (1 / 4)) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨(1 - Real.sqrt (1 - 4 * (v : ℝ))) / 2,
    by
      have hv : 0 ≤ 1 - 4 * (v : ℝ) := by linarith only [v.property.2]
      have hs : Real.sqrt (1 - 4 * (v : ℝ)) ≤ 1 := by
        rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)]
        nlinarith only [v.property.1]
      exact ⟨by linarith, by linarith [Real.sqrt_nonneg (1 - 4 * (v : ℝ))]⟩⟩

private theorem variance_probabilityOfVariance (v : Set.Icc (0 : ℝ) (1 / 4)) :
    (probabilityOfVariance v : ℝ) * (1 - probabilityOfVariance v) = (v : ℝ) := by
  have hv : 0 ≤ 1 - 4 * (v : ℝ) := by linarith only [v.property.2]
  change ((1 - Real.sqrt (1 - 4 * (v : ℝ))) / 2) *
    (1 - (1 - Real.sqrt (1 - 4 * (v : ℝ))) / 2) = (v : ℝ)
  nlinarith only [Real.sq_sqrt hv]

/-- Lemma A.1 for arbitrary positive weights in a fixed interval. The
lower quadratic bound uses the number of vertices outside the deleted clique. -/
theorem weightedDegreeMatrix_outside_overlap_bounds (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (w : Edge α → ℝ) {lower upper : ℝ} (hlower : 0 < lower)
    (hupper : 0 < upper) (hw : ∀ e, w e ∈ Set.Icc lower upper) :
    let n : ℝ := Fintype.card α
    let m : ℝ := ((Finset.univ : Finset α) \ S).card
    let c := lower * (m ^ 2 / (3 * n))
    let Q := weightedDegreeMatrix (edgesOutsideOverlap S) w
    let r := upper / c ^ 2 + n * upper ^ 2 / c ^ 3
    (∀ v : α → ℝ, c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) ∧
      v ⬝ᵥ (Q *ᵥ v) ≤ 2 * upper * (n - 1) * ∑ i, v i ^ 2) ∧
    IsUnit Q.det ∧ (∀ i, |Q⁻¹ i i| ≤ c⁻¹) ∧
      (∀ i j, i ≠ j → |Q⁻¹ i j| ≤ r) ∧
      (∀ i, (∑ j, |Q⁻¹ i j|) ≤ c⁻¹ + n * r) := by
  classical
  intro n m c Q r
  let g (e : Edge α) : Set.Icc (0 : ℝ) (1 / 4) :=
    ⟨w e / (4 * upper), div_nonneg (hlower.le.trans (hw e).1) (by positivity),
      (div_le_iff₀ (by positivity : 0 < 4 * upper)).mpr (by linarith only [(hw e).2])⟩
  let p (e : Edge α) := probabilityOfVariance (g e)
  let A := edgesOutsideOverlap S
  have hvar (e : Edge α) : (p e : ℝ) * (1 - p e) = w e / (4 * upper) :=
    variance_probabilityOfVariance (g e)
  have hscale (i j : α) : Q i j = 4 * upper * degreeCovariance A p i j := by
    change (∑ e ∈ A, w e * (edgeIncidence e i : ℝ) * (edgeIncidence e j : ℝ)) = _
    simp only [degreeCovariance, hvar, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    field_simp
  have hn₀ : 0 < n := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega)
    ((show 3 ≤ ((Finset.univ : Finset α) \ S).card from hm).trans (Finset.card_le_univ _)))
  have hm₀ : 0 < m := Nat.cast_pos.mpr (by omega)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcoeff (e : Edge α) : lower / (4 * upper) ≤ (p e : ℝ) * (1 - p e) := by
    rw [hvar]
    exact div_le_div_of_nonneg_right (hw e).1 (by positivity)
  have hquad (v : α → ℝ) : c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) ∧
      v ⬝ᵥ (Q *ᵥ v) ≤ 2 * upper * (n - 1) * ∑ i, v i ^ 2 := by
    obtain ⟨hL, hU⟩ := degreeCovariance_outside_overlap_bounds S hm p _ (by positivity) hcoeff v
    change lower / (4 * upper) * (m ^ 2 / (3 * n)) * (∑ i, v i ^ 2) ≤ _ at hL
    change _ ≤ (n - 1) / 2 * (∑ i, v i ^ 2) at hU
    have heq : v ⬝ᵥ (Q *ᵥ v) = (4 * upper) * ∑ i, ∑ j, v i * degreeCovariance A p i j * v j := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hscale, mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    have hpos : (0 : ℝ) ≤ 4 * upper := by positivity
    constructor
    · have h := mul_le_mul_of_nonneg_left hL hpos
      convert h using 1
      dsimp only [c]
      field_simp
    · have h := mul_le_mul_of_nonneg_left hU hpos
      convert h using 1 <;> ring
  have hdet := (inverse_mulVec_sq_le_of_quadratic Q hc (fun v ↦ (hquad v).1)).1
  have hoff (i j : α) (hij : i ≠ j) : |Q i j| ≤ upper := by
    rw [hscale, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * upper)]
    have h := mul_le_mul_of_nonneg_left (degreeCovariance_offDiag_le A p hij)
      (show 0 ≤ 4 * upper by positivity)
    linarith only [h]
  obtain ⟨hd, ho⟩ := inverse_entry_bounds Q hc hupper.le (fun v ↦ (hquad v).1) hoff
  refine ⟨hquad, hdet, hd, ho, ?_⟩
  intro i
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  rw [← Finset.sum_erase_add Finset.univ (fun j ↦ |Q⁻¹ i j|) (Finset.mem_univ i)]
  calc
    _ ≤ (∑ _ ∈ Finset.univ.erase i, r) + c⁻¹ := by
      exact add_le_add (Finset.sum_le_sum (fun j hj ↦ ho i j
        (Ne.symm (Finset.ne_of_mem_erase hj)))) (hd i)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, add_comm]
      have hk : ((Finset.univ.erase i).card : ℝ) ≤ n :=
        Nat.cast_le.mpr (Finset.card_le_univ (Finset.univ.erase i))
      exact add_le_add_right (mul_le_mul_of_nonneg_right hk hr) _

/-- The fixed-fraction version of Lemma A.1, with explicit coefficients
for the inverse bounds as functions of the weight interval and overlap fraction. -/
theorem weightedDegreeMatrix_outside_overlap_fixedFraction (S : Finset α)
    (w : Edge α → ℝ) {lower upper ρ : ℝ} (hlower : 0 < lower) (hupper : 0 < upper)
    (hw : ∀ e, w e ∈ Set.Icc lower upper) (hρ : ρ < 1)
    (hS : (S.card : ℝ) ≤ ρ * Fintype.card α)
    (hn : 3 ≤ (1 - ρ) * Fintype.card α) :
    let n : ℝ := Fintype.card α
    let c₀ := lower * (1 - ρ) ^ 2 / 3
    let r₀ := upper / c₀ ^ 2 + upper ^ 2 / c₀ ^ 3
    let Q := weightedDegreeMatrix (edgesOutsideOverlap S) w
    (∀ v : α → ℝ, c₀ * n * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) ∧
      v ⬝ᵥ (Q *ᵥ v) ≤ 2 * upper * (n - 1) * ∑ i, v i ^ 2) ∧
    IsUnit Q.det ∧ (∀ i, |Q⁻¹ i i| ≤ c₀⁻¹ / n) ∧
      (∀ i j, i ≠ j → |Q⁻¹ i j| ≤ r₀ / n ^ 2) ∧
      (∀ i, (∑ j, |Q⁻¹ i j|) ≤ (c₀⁻¹ + r₀) / n) := by
  classical
  intro n c₀ r₀ Q
  let m : ℝ := ((Finset.univ : Finset α) \ S).card
  let c := lower * (m ^ 2 / (3 * n))
  let r := upper / c ^ 2 + n * upper ^ 2 / c ^ 3
  have hcount : m + S.card = n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ] at h
    dsimp only [m, n]
    exact_mod_cast h
  have hm : (1 - ρ) * n ≤ m := by linarith only [hS, hcount]
  have hm' : (3 : ℝ) ≤ m := hn.trans hm
  have hm₃ : 3 ≤ ((Finset.univ : Finset α) \ S).card := by
    dsimp only [m] at hm'
    exact_mod_cast hm'
  have hn₀ : 0 < n := by linarith only [hcount, hm', Nat.cast_nonneg (α := ℝ) S.card]
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact div_pos (mul_pos hlower (sq_pos_of_pos (sub_pos.mpr hρ))) (by norm_num)
  have hlin : c₀ * n ≤ c := by
    have hs := pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hρ.le) hn₀.le) hm 2
    calc
      _ = lower * (((1 - ρ) * n) ^ 2 / (3 * n)) := by
        dsimp only [c₀]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (by positivity)) hlower.le
  obtain ⟨hquad, hdet, hd, ho, hrow⟩ :=
    weightedDegreeMatrix_outside_overlap_bounds S hm₃ w hlower hupper hw
  change (∀ v : α → ℝ, c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) ∧
    v ⬝ᵥ (Q *ᵥ v) ≤ 2 * upper * (n - 1) * ∑ i, v i ^ 2) at hquad
  have hdc : c⁻¹ ≤ c₀⁻¹ / n := by
    calc
      _ ≤ (c₀ * n)⁻¹ := (inv_le_inv₀
        ((mul_pos hc₀ hn₀).trans_le hlin) (mul_pos hc₀ hn₀)).2 hlin
      _ = _ := by rw [mul_inv, div_eq_mul_inv]
  have hro : r ≤ r₀ / n ^ 2 := by
    calc
      _ ≤ upper / (c₀ * n) ^ 2 + n * upper ^ 2 / (c₀ * n) ^ 3 := by
        dsimp only [r]
        gcongr
      _ = _ := by
        dsimp only [r₀]
        field_simp
  have hrows : c⁻¹ + n * r ≤ (c₀⁻¹ + r₀) / n := by
    calc
      _ ≤ c₀⁻¹ / n + n * (r₀ / n ^ 2) :=
        add_le_add hdc (mul_le_mul_of_nonneg_left hro hn₀.le)
      _ = _ := by field_simp
  refine ⟨fun v ↦ ⟨?_, (hquad v).2⟩, hdet, fun i ↦ (hd i).trans hdc,
    fun i j hij ↦ (ho i j hij).trans hro, fun i ↦ (hrow i).trans hrows⟩
  exact (mul_le_mul_of_nonneg_right hlin (Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i))).trans
    (hquad v).1

end BoundedEdgeRegularSubgraphs
