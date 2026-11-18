module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Inverse estimates for the covariance argument
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive quadratic-form bound controls the squared Euclidean norm of the inverse. -/
theorem inverse_mulVec_sq_le_of_quadratic (A : Matrix ι ι ℝ)
    {c : ℝ} (hc : 0 < c)
    (hquad : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) :
    IsUnit A.det ∧ ∀ z : ι → ℝ, (∑ i, (A⁻¹ *ᵥ z) i ^ 2) ≤ (∑ i, z i ^ 2) / c ^ 2 := by
  have hzero (x : ι → ℝ) (hx : A *ᵥ x = 0) : x = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      contrapose! hne
      exact funext hne
    have hs : 0 < ∑ j, x j ^ 2 :=
      Finset.sum_pos' (fun j _ ↦ sq_nonneg (x j))
        ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have h := hquad x
    rw [hx, dotProduct_zero] at h
    exact (mul_pos hc hs).not_ge h
  have hinj : Function.Injective (fun x ↦ A *ᵥ x) := by
    intro x y hxy
    change A *ᵥ x = A *ᵥ y at hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  refine ⟨hdet, ?_⟩
  intro z
  let y := A⁻¹ *ᵥ z
  let S : ℝ := ∑ i, y i ^ 2
  let T : ℝ := ∑ i, z i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (y i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (z i))
  change S ≤ T / c ^ 2
  rcases hS.eq_or_lt with h | h
  · rw [← h]
    exact div_nonneg hT (sq_nonneg c)
  have hsolve : A *ᵥ y = z := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hlo : c * S ≤ y ⬝ᵥ z := by
    rw [← hsolve]
    exact hquad y
  have hdot : 0 ≤ y ⬝ᵥ z := (mul_nonneg hc.le hS).trans hlo
  have hsquare : (c * S) ^ 2 ≤ (y ⬝ᵥ z) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc.le hS) hdot).mpr hlo
  have hcs : (y ⬝ᵥ z) ^ 2 ≤ S * T :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y z
  have hmul : (S * c ^ 2) * S ≤ T * S := by
    nlinarith only [hsquare.trans hcs]
  exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (le_of_mul_le_mul_right hmul h)

/-- The exact two-step resolvent identity used for off-diagonal inverse entries. -/
theorem inverse_second_order (A B W : Matrix ι ι ℝ)
    (h : A = B + W) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ = B⁻¹ - B⁻¹ * W * B⁻¹ + B⁻¹ * W * A⁻¹ * W * B⁻¹ := by
  have hleft : A⁻¹ = B⁻¹ - B⁻¹ * W * A⁻¹ := by
    apply eq_sub_of_add_eq
    calc
      _ = (B⁻¹ * B + B⁻¹ * W) * A⁻¹ := by
        rw [add_mul, Matrix.nonsing_inv_mul B hB, one_mul]
      _ = B⁻¹ * (A * A⁻¹) := by rw [h]; noncomm_ring
      _ = _ := by rw [Matrix.mul_nonsing_inv A hA, mul_one]
  have hright : A⁻¹ = B⁻¹ - A⁻¹ * W * B⁻¹ := by
    apply eq_sub_of_add_eq
    calc
      _ = A⁻¹ * (B * B⁻¹ + W * B⁻¹) := by
        rw [mul_add, Matrix.mul_nonsing_inv B hB, mul_one]
        noncomm_ring
      _ = (A⁻¹ * A) * B⁻¹ := by rw [h]; noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul A hA, one_mul]
  calc
    _ = B⁻¹ - B⁻¹ * W * A⁻¹ := hleft
    _ = B⁻¹ - B⁻¹ * W * (B⁻¹ - A⁻¹ * W * B⁻¹) := by rw [← hright]
    _ = _ := by noncomm_ring

/-- A coercive real matrix with bounded off-diagonal entries has a
reciprocal-scale diagonal and a smaller off-diagonal scale in its inverse. -/
theorem inverse_entry_bounds (A : Matrix ι ι ℝ)
    {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hquad : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x))
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ b) :
    (∀ i, |A⁻¹ i i| ≤ c⁻¹) ∧
    (∀ i j, i ≠ j → |A⁻¹ i j| ≤ b / c ^ 2 + (Fintype.card ι : ℝ) * b ^ 2 / c ^ 3) := by
  classical
  obtain ⟨hdet, hinverse⟩ := inverse_mulVec_sq_le_of_quadratic A hc hquad
  have hbasis (j : ι) : (∑ i : ι, ((Pi.single j 1 : ι → ℝ) i) ^ 2) = (1 : ℝ) := by
    simp [Pi.single_apply, apply_ite (fun x : ℝ ↦ x ^ 2)]
  constructor
  · intro j
    have h := hinverse (Pi.single j 1)
    rw [Matrix.mulVec_single_one, hbasis] at h
    have he : (A⁻¹ j j) ^ 2 ≤ ∑ i, (A⁻¹ i j) ^ 2 :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg (A⁻¹ i j)) (Finset.mem_univ j)
    have hsq : |A⁻¹ j j| ^ 2 ≤ c⁻¹ ^ 2 := by
      rw [sq_abs, inv_pow, ← one_div (c ^ 2)]
      exact he.trans h
    exact (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr hc.le)).mp hsq
  have hdiag (i : ι) : c ≤ A i i := by
    have h := hquad (Pi.single i 1)
    rw [hbasis, mul_one, Matrix.mulVec_single_one] at h
    simpa [dotProduct, Pi.single_apply, Matrix.col] using h
  let B := Matrix.diagonal (fun i ↦ A i i)
  let W := A - B
  let G := Matrix.diagonal (fun i ↦ (A i i)⁻¹)
  have hB : IsUnit B.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hc.trans_le (hdiag i)).ne')
  have hG : B⁻¹ = G := by
    have hBG : B * G = 1 := by
      dsimp only [B, G]
      rw [Matrix.diagonal_mul_diagonal]
      have hdiag_prod : (fun i ↦ A i i * (A i i)⁻¹) = fun _ ↦ (1 : ℝ) := by
        funext i
        exact mul_inv_cancel₀ (hc.trans_le (hdiag i)).ne'
      rw [hdiag_prod, Matrix.diagonal_one]
    calc
      _ = B⁻¹ * (B * G) := by rw [hBG, mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, one_mul]
  have hW (i j : ι) : |W i j| ≤ b := by
    by_cases hij : i = j
    · subst j
      simpa [W, B] using hb
    · simpa [W, B, Matrix.diagonal_apply_ne _ hij] using hoff i j hij
  have hsquare (x : ℝ) (hx : |x| ≤ b) : x ^ 2 ≤ b ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hb).mpr hx
  let N := (Fintype.card ι : ℝ) * b ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hrow (i : ι) : ∑ j, (W i j) ^ 2 ≤ N := by
    calc
      _ ≤ ∑ _ : ι, b ^ 2 :=
        Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hsquare (W i j) (hW i j))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcol (j : ι) : ∑ i, (W i j) ^ 2 ≤ N := by
    calc
      _ ≤ ∑ _ : ι, b ^ 2 :=
        Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hsquare (W i j) (hW i j))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hrem (i j : ι) : |(W * A⁻¹ * W) i j| ≤ N / c := by
    let z (k : ι) := W k j
    let y := A⁻¹ *ᵥ z
    have hy : (∑ k, y k ^ 2) ≤ N / c ^ 2 :=
      (hinverse z).trans (div_le_div_of_nonneg_right (hcol j) (sq_nonneg c))
    have he : (W * A⁻¹ * W) i j = ∑ k, W i k * y k := by
      rw [Matrix.mul_assoc]
      rfl
    rw [he]
    apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg hN hc.le)).mp
    rw [sq_abs]
    calc
      _ ≤ (∑ k, W i k ^ 2) * (∑ k, y k ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k ↦ W i k) y
      _ ≤ N * (N / c ^ 2) :=
        mul_le_mul (hrow i) hy (Finset.sum_nonneg fun k _ ↦ sq_nonneg (y k)) hN
      _ = _ := by ring
  have hcoeff (i : ι) : |(A i i)⁻¹| ≤ c⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr (hc.trans_le (hdiag i)).le)]
    exact inv_anti₀ hc (hdiag i)
  have htriple (i j : ι) (x r : ℝ) (hx : |x| ≤ r) :
      |(A i i)⁻¹ * x * (A j j)⁻¹| ≤ c⁻¹ * r * c⁻¹ := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hcoeff i) hx (abs_nonneg _) (inv_nonneg.mpr hc.le))
      (hcoeff j) (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr hc.le) ((abs_nonneg _).trans hx))
  have hexpand : A⁻¹ = G - G * W * G + G * (W * A⁻¹ * W) * G := by
    have he := inverse_second_order A B W (show A = B + W by dsimp [W]; abel) hdet hB
    rw [hG] at he
    simpa only [Matrix.mul_assoc] using he
  intro i j hij
  have hentry : A⁻¹ i j =
      -((A i i)⁻¹ * W i j * (A j j)⁻¹) +
        (A i i)⁻¹ * (W * A⁻¹ * W) i j * (A j j)⁻¹ := by
    have h := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hexpand
    simp [G, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_apply_ne _ hij] at h
    exact h
  rw [hentry]
  calc
    _ ≤ |-( (A i i)⁻¹ * W i j * (A j j)⁻¹)| +
        |(A i i)⁻¹ * (W * A⁻¹ * W) i j * (A j j)⁻¹| := abs_add_le _ _
    _ ≤ c⁻¹ * b * c⁻¹ + c⁻¹ * (N / c) * c⁻¹ := by
      rw [abs_neg]
      exact add_le_add (htriple i j _ _ (hW i j)) (htriple i j _ _ (hrem i j))
    _ = _ := by dsimp [N]; ring

end BoundedEdgeRegularSubgraphs
