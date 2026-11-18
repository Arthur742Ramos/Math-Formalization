module

public import BoundedEdgeRegularSubgraphs.OverlapInverse
public import BoundedEdgeRegularSubgraphs.DeterminantRatio
import Mathlib.Tactic

/-!
# The covariance determinant cost of conditioning on shared edges
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
private theorem covariance_hermitian (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1) :
    (degreeCovariance A p).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, degreeCovariance]
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

private theorem covariance_dot_product (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    (v : α → ℝ) :
    v ⬝ᵥ (degreeCovariance A p *ᵥ v) = ∑ i, ∑ j, v i * degreeCovariance A p i j * v j := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]

omit [Fintype α] in
private theorem covariance_rank_one (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1) :
    degreeCovariance A p =
      ∑ e ∈ A, ((p e : ℝ) * (1 - p e)) •
        vecMulVec (fun i ↦ (edgeIncidence e i : ℝ)) (fun i ↦ (edgeIncidence e i : ℝ)) := by
  ext i j
  simp only [degreeCovariance, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

private theorem inverse_quadratic_le (A : Matrix α α ℝ) {c : ℝ} (hc : 0 < c)
    (hquad : ∀ x : α → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) (v : α → ℝ) :
    v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ (∑ i, v i ^ 2) / c := by
  let s := ∑ i, v i ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hnorm := (inverse_mulVec_sq_le_of_quadratic A hc hquad).2 v
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (A⁻¹ *ᵥ v)
  change (v ⬝ᵥ (A⁻¹ *ᵥ v)) ^ 2 ≤ s * (∑ i, (A⁻¹ *ᵥ v) i ^ 2) at hcs
  have h := hcs.trans (mul_le_mul_of_nonneg_left hnorm hs)
  change (v ⬝ᵥ (A⁻¹ *ᵥ v)) ^ 2 ≤ s * (s / c ^ 2) at h
  rw [← mul_div_assoc, ← pow_two, ← div_pow] at h
  change v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ s / c
  by_contra! hn
  have hp : 0 ≤ s / c := div_nonneg hs hc.le
  exact (not_lt_of_ge h) ((sq_lt_sq₀ hp (hp.trans hn.le)).mpr hn)

private theorem sum_incidence_sq (e : Edge α) :
    (∑ i, (edgeIncidence e i : ℝ) ^ 2) = 2 := by
  classical
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have ht (i : α) : (edgeIncidence e i : ℝ) ^ 2 =
      (if i = e.val.1 then (1 : ℝ) else 0) + (if i = e.val.2 then 1 else 0) := by
    by_cases hi : i = e.val.1
    · subst i
      simp [edgeIncidence, he]
    · by_cases hj : i = e.val.2 <;> simp [edgeIncidence, hi, hj, he.symm]
  norm_num [ht, Finset.sum_add_distrib]

/-- The determinant comparison in Corollary C.2, with the size of the
deleted clique and the lower spectral constant made explicit. -/
theorem degreeCovariance_det_overlap_le (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (p : Edge α → Set.Icc (0 : ℝ) 1) (lower : ℝ) (hlower : 0 < lower)
    (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e)) :
    let c : ℝ := lower * ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α))
    (degreeCovariance Finset.univ p).det ≤
      (degreeCovariance (edgesOutsideOverlap S) p).det *
        Real.exp ((S.card : ℝ) * ((S.card : ℝ) - 1) / (4 * c)) := by
  classical
  let A := edgesOutsideOverlap S
  let I := Finset.univ.filter (fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S)
  let Q := degreeCovariance A p
  let P := degreeCovariance I p
  intro c
  have hk : 0 < Fintype.card α :=
    (show 0 < ((Finset.univ : Finset α) \ S).card by omega).trans_le (Finset.card_le_univ _)
  have hc : 0 < c := by dsimp [c]; positivity
  have hquad (v : α → ℝ) : c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) := by
    simpa only [Q, A, covariance_dot_product] using
      (degreeCovariance_outside_overlap_bounds S hm p lower hlower.le hp v).1
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (covariance_hermitian _ p)
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      contrapose! hv
      exact funext hv
    have hs : 0 < ∑ i, v i ^ 2 :=
      Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    rw [star_trivial]
    exact (mul_pos hc hs).trans_le (hquad v)
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (covariance_hermitian _ p)
    intro v
    rw [star_trivial, covariance_dot_product]
    exact degreeCovariance_quadratic_nonneg I p v
  have hadd : Q + P = degreeCovariance Finset.univ p := by
    ext i j
    simp only [Matrix.add_apply, Q, P, degreeCovariance]
    rw [add_comm]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S) _
  have htrace : (Q⁻¹ * P).trace ≤ (I.card : ℝ) * (1 / (2 * c)) := by
    dsimp only [P]
    have hconst : (∑ _ ∈ I, (1 / (2 * c) : ℝ)) = (I.card : ℝ) * (1 / (2 * c)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [covariance_rank_one, Finset.mul_sum, Matrix.trace_sum, ← hconst]
    have he (e : Edge α) : (p e : ℝ) * (1 - p e) ∈ Set.Icc (0 : ℝ) (1 / 4) := by
      refine ⟨mul_nonneg (p e).property.1 (sub_nonneg.mpr (p e).property.2), ?_⟩
      nlinarith only [sq_nonneg ((p e : ℝ) - 1 / 2)]
    apply Finset.sum_le_sum
    intro e _
    let v := fun i : α ↦ (edgeIncidence e i : ℝ)
    let w := (p e : ℝ) * (1 - p e)
    change (Q⁻¹ * (w • vecMulVec v v)).trace ≤ 1 / (2 * c)
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm, smul_eq_mul]
    have h := inverse_quadratic_le Q hc hquad v
    change v ⬝ᵥ (Q⁻¹ *ᵥ v) ≤ (∑ i, (edgeIncidence e i : ℝ) ^ 2) / c at h
    rw [sum_incidence_sq] at h
    calc
      _ ≤ w * (2 / c) := mul_le_mul_of_nonneg_left h (he e).1
      _ ≤ (1 / 4 : ℝ) * (2 / c) := mul_le_mul_of_nonneg_right (he e).2 (by positivity)
      _ = _ := by ring
  have hcard : 2 * (I.card : ℝ) = (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have h := sum_edges_inside S (fun _ ↦ (1 : ℝ))
    change (∑ _ ∈ I, ((1 : ℝ) + 1) ^ 2) =
      ((S.card : ℝ) - 2) * (∑ _ ∈ S, (1 : ℝ) ^ 2) + (∑ _ ∈ S, (1 : ℝ)) ^ 2 at h
    simp only [Finset.sum_const, nsmul_eq_mul, one_pow, mul_one] at h
    nlinarith only [h]
  have hr : (I.card : ℝ) * (1 / (2 * c)) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) / (4 * c) := by
    rw [← hcard]
    ring
  rw [← hadd]
  refine (det_add_le_det_mul_exp_trace Q P hQ hP).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (htrace.trans_eq hr)) hQ.det_pos.le

end BoundedEdgeRegularSubgraphs
