/- AI-assisted formalization under the repository Apache-2.0 license.
Actual payoff scaling, for extending unit-bound joint-support constructions. -/
module
public import JointSupportGeneral
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem response_payoff_scale {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) (c : ℝ) (i : ι) :
    response (fun a b => c*A a b) x i=c*response A x i := by
  simp only [response, mul_assoc, Finset.mul_sum]

theorem block_payoff_scale {α ι : Type*}
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ) (c : ℝ) :
    blockMatrix (fun a b => c*K a b) (fun i a => c*D i a) (fun i j => c*B i j)=
      fun a b => c*blockMatrix K D B a b := by
  funext a b
  cases a <;> cases b <;> simp only [blockMatrix, mul_neg]

theorem inverse_sqrt_tolerance_scale (M η : ℝ) :
    1/Real.sqrt (η/M)=Real.sqrt (M/η) := by
  rw [show η/M=(M/η)⁻¹ by simp only [inv_div], Real.sqrt_inv]
  simp only [one_div, inv_inv]

end
end SparseCompletion
