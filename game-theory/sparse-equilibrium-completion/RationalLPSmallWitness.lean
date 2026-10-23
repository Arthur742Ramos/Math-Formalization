/- AI-assisted formalization under repository Apache-2.0.
Feasibility plus earned coordinate boundedness yields a small
rational feasible point via an earned original-row basis and Cramer quotients.
No solver output or polynomial-time algorithm theorem is asserted. -/
module
public import RationalLPActiveBasis
public import RationalLPCramerHeight
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion

theorem rational_lp_small_witness_height_formula (rows vars B : ℕ) :
    rationalLPSmallWitnessHeight rows vars B = vars*vars+vars*(B*(rows*(vars+1)+1)) := rfl

theorem rational_lp_integer_selected_det_ne_zero {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (e : Fin n → I)
    (hdet : Matrix.det (fun i j => S.coefficient (e i) j : Matrix (Fin n) (Fin n) ℚ) ≠ 0) :
    Matrix.det (fun i j => rationalLPIntegerInput S (e i) (some j) : Matrix (Fin n) (Fin n) ℤ) ≠ 0 := by
  let A : Matrix (Fin n) (Fin n) ℤ := fun i j => rationalLPIntegerInput S (e i) (some j)
  let C : Matrix (Fin n) (Fin n) ℚ := fun i j => S.coefficient (e i) j
  have hm : A.map (fun z : ℤ => (z : ℚ)) =
      (rationalLPInputDenominator S : ℚ) • C := by
    ext i j
    exact rational_lp_integer_input_cast S (e i) (some j)
  have hD : (rationalLPInputDenominator S : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rational_lp_input_denominator_positive S))
  have hz : (A.det : ℚ) ≠ 0 := by
    rw [Int.cast_det, hm, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hD) hdet
  change A.det ≠ 0
  exact_mod_cast hz

theorem rational_lp_integer_selected_real_equations {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (e : Fin n → I) (x : Fin n → ℝ)
    (he : ∀ i, rationalLPRealResponse S x (e i) = (S.rightSide (e i) : ℝ)) :
    (fun i j => (rationalLPIntegerInput S (e i) (some j) : ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x =
      fun i => (rationalLPIntegerInput S (e i) none : ℝ) := by
  funext i
  change (∑ j, (rationalLPIntegerInput S (e i) (some j) : ℝ)*x j) = _
  simp only [rational_lp_integer_input_real_cast]
  change (∑ j, (rationalLPInputDenominator S : ℝ)*(S.coefficient (e i) j : ℝ)*x j) =
    (rationalLPInputDenominator S : ℝ)*(S.rightSide (e i) : ℝ)
  calc
    _ = (rationalLPInputDenominator S : ℝ)*rationalLPRealResponse S x (e i) := by
      unfold rationalLPRealResponse
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := congrArg ((rationalLPInputDenominator S : ℝ)*·) (he i)

/-- Main certificate-existence statement. Input component bounds and the
same feasible set's coordinate bounds are the only quantitative premises.
The selected original active basis, all denominators, and the rational
witness are earned in the proof. -/
theorem rational_lp_exists_small_feasible_point {I : Type*} [Fintype I] {n B : ℕ}
    (S : RationalLinearSystem I n)
    (hc : ∀ row j, RationalInputHeight (S.coefficient row j) B)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) B)
    (U : Fin n → ℝ) (hb : ∀ y, S.RealSatisfies y → ∀ j, |y j| ≤ U j)
    (hf : ∃ x, S.RealSatisfies x) :
    ∃ q, S.Satisfies q ∧ ∀ j,
      RationalInputHeight (q j) (rationalLPSmallWitnessHeight (Fintype.card I) n B) := by
  obtain ⟨x,e,hx,_he,hactive,hdet⟩ := rational_lp_exists_active_basis S U hb hf
  let A : Matrix (Fin n) (Fin n) ℤ := fun i j => rationalLPIntegerInput S (e i) (some j)
  let b : Fin n → ℤ := fun i => rationalLPIntegerInput S (e i) none
  have hA : A.det ≠ 0 := rational_lp_integer_selected_det_ne_zero S e hdet
  let q := rationalIntegerCramerWitness A b
  have hreal : (fun j => (q j : ℝ)) = x := rational_integer_cramer_witness_real_eq A b hA x
    (rational_lp_integer_selected_real_equations S e x hactive)
  refine ⟨q,(rational_linear_real_cast_iff S q).mp ?_,?_⟩
  · rw [hreal]
    exact hx
  · exact rational_integer_cramer_witness_input_height A b hA
      (fun i j => rational_lp_integer_input_entry_bound S hc hr (e i) (some j))
      (fun i => rational_lp_integer_input_entry_bound S hc hr (e i) none)

end SparseCompletion
