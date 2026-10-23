/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalLinearTransfer
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFormAdd {n : ℕ} (c d : Fin n → ℚ) : Fin n → ℚ := fun u => c u+d u
def rationalFormScale {n : ℕ} (a : ℚ) (c : Fin n → ℚ) : Fin n → ℚ := fun u => a*c u
def rationalFormSum {n : ℕ} {I : Type*} [Fintype I] (c : I → Fin n → ℚ) : Fin n → ℚ :=
  fun u => ∑ i, c i u

def rationalFormEval {n : ℕ} (c x : Fin n → ℚ) : ℚ := ∑ u, c u*x u
def rationalFormRealEval {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) : ℝ :=
  ∑ u, (c u : ℝ)*x u

theorem rational_form_eval_add {n : ℕ} (c d x : Fin n → ℚ) :
    rationalFormEval (rationalFormAdd c d) x=rationalFormEval c x+rationalFormEval d x := by
  simp only [rationalFormEval,rationalFormAdd,add_mul,Finset.sum_add_distrib]

theorem rational_form_eval_scale {n : ℕ} (a : ℚ) (c x : Fin n → ℚ) :
    rationalFormEval (rationalFormScale a c) x=a*rationalFormEval c x := by
  simp only [rationalFormEval,rationalFormScale,mul_assoc,Finset.mul_sum]

theorem rational_form_eval_sum {n : ℕ} {I : Type*} [Fintype I]
    (c : I → Fin n → ℚ) (x : Fin n → ℚ) :
    rationalFormEval (rationalFormSum c) x=∑ i, rationalFormEval (c i) x := by
  simp only [rationalFormEval,rationalFormSum,Finset.sum_mul]
  exact Finset.sum_comm

theorem rational_form_real_eval_add {n : ℕ} (c d : Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormAdd c d) x=
      rationalFormRealEval c x+rationalFormRealEval d x := by
  simp only [rationalFormRealEval,rationalFormAdd,Rat.cast_add,add_mul,Finset.sum_add_distrib]

theorem rational_form_real_eval_scale {n : ℕ} (a : ℚ) (c : Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormScale a c) x=(a : ℝ)*rationalFormRealEval c x := by
  simp only [rationalFormRealEval,rationalFormScale,Rat.cast_mul,mul_assoc,Finset.mul_sum]

theorem rational_form_real_eval_sum {n : ℕ} {I : Type*} [Fintype I]
    (c : I → Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormSum c) x=∑ i, rationalFormRealEval (c i) x := by
  simp only [rationalFormRealEval,rationalFormSum,Rat.cast_sum,Finset.sum_mul]
  exact Finset.sum_comm

end SparseCompletion
