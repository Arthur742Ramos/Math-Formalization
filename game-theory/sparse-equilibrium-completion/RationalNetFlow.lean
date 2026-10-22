/- AI-assisted formalization under the repository Apache-2.0 license.
Bridge raw nonnegative arc flows to skew net flows. Residual capacity C-netF
includes both unused forward capacity and cancellable reverse flow. No
augmentation algorithm or polynomial bound is asserted. -/
module
public import RationalResidualReach
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalNetFlow {n : ℕ} (F : Fin n → Fin n → ℚ) (u v : Fin n) : ℚ :=
  F u v-F v u

theorem rational_net_flow_skew {n : ℕ} (F : Fin n → Fin n → ℚ) (u v : Fin n) :
    rationalNetFlow F u v= -rationalNetFlow F v u := by
  unfold rationalNetFlow
  ring

theorem rational_net_flow_capacity {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hf : ∀ u v, 0 ≤ F u v ∧ F u v ≤ C u v) (u v : Fin n) :
    rationalNetFlow F u v ≤ C u v := by
  have hh := (hf u v).2
  have hr := (hf v u).1
  unfold rationalNetFlow
  linarith

theorem rational_net_flow_residual_identity {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (u v : Fin n) : C u v-rationalNetFlow F u v = C u v-F u v+F v u := by
  unfold rationalNetFlow
  ring

theorem rational_net_flow_residual_nonnegative {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hf : ∀ u v, 0 ≤ F u v ∧ F u v ≤ C u v) (u v : Fin n) :
    0 ≤ C u v-rationalNetFlow F u v :=
  sub_nonneg.mpr (rational_net_flow_capacity C F hf u v)

theorem rational_net_flow_divergence {n : ℕ} (F : Fin n → Fin n → ℚ) (u : Fin n) :
    (∑ v, rationalNetFlow F u v)=(∑ v, F u v)-(∑ v, F v u) := by
  simp only [rationalNetFlow,Finset.sum_sub_distrib]

theorem rational_saturated_net_flow_demand {n : ℕ} (d : Fin n → ℚ)
    (C F : Fin n → Fin n → ℚ) (y : Fin n → ℚ)
    (hf : RationalSaturatedFlow d C F y) (u : Fin n) :
    d u ≤ ∑ v, rationalNetFlow F u v := by
  rw [rational_net_flow_divergence]
  exact rational_saturated_flow_divergence d C F y hf u

theorem rational_net_flow_decode_identity {n : ℕ} (q : Fin n → ℚ)
    (F : Fin n → Fin n → ℚ) (u v : Fin n) :
    rationalFlowDecode q F u v= -rationalNetFlow F u v/(q u*q v) := rfl

end SparseCompletion
