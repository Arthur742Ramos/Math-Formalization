/- AI-assisted formalization under the repository Apache-2.0 license.
An explicitly checkable saturated-source flow certificate. This is not an
existence theorem, a flow finder, or a polynomial algorithm guarantee. -/
module
public import RationalFlowDemandCuts
public import RationalResidualCompletion
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalSaturatedFlow {m : ℕ} (d : Fin m → ℚ) (c F : Fin m → Fin m → ℚ)
    (y : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ max (-d i) 0) ∧
  (∀ i j, 0 ≤ F i j ∧ F i j ≤ c i j) ∧
  ∀ i, max (d i) 0+(∑ j, F j i) = y i+(∑ j, F i j)

instance rationalSaturatedFlowDecidable {m : ℕ} (d : Fin m → ℚ)
    (c F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) :
    Decidable (RationalSaturatedFlow d c F y) := by
  unfold RationalSaturatedFlow
  infer_instance

theorem rational_saturated_flow_divergence {m : ℕ} (d : Fin m → ℚ)
    (c F : Fin m → Fin m → ℚ) (y : Fin m → ℚ)
    (hf : RationalSaturatedFlow d c F y) (i : Fin m) :
    d i ≤ (∑ j, F i j)-(∑ j, F j i) := by
  have hh := hf.2.2 i
  have hy := (hf.1 i).2
  have hd := rational_demand_parts (d i)
  linarith

def rationalFlowDecode {m : ℕ} (q : Fin m → ℚ) (F : Fin m → Fin m → ℚ) :
    Fin m → Fin m → ℚ := fun i j => -(F i j-F j i)/(q i*q j)

theorem rational_flow_decode_skew {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (i j : Fin m) :
    rationalFlowDecode q F i j= -rationalFlowDecode q F j i := by
  unfold rationalFlowDecode
  rw [mul_comm (q j) (q i)]
  ring

theorem rational_flow_decode_bounds {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ) (hq : ∀ i, 0 < q i)
    (hf : ∀ i j, 0 ≤ F i j ∧ F i j ≤ M*q i*q j) (i j : Fin m) :
    -M ≤ rationalFlowDecode q F i j ∧ rationalFlowDecode q F i j ≤ M := by
  have hqq := mul_pos (hq i) (hq j)
  have hij := hf i j
  have hji := hf j i
  unfold rationalFlowDecode
  constructor
  · apply (le_div_iff₀ hqq).mpr
    nlinarith
  · apply (div_le_iff₀ hqq).mpr
    nlinarith

theorem rational_flow_decode_response_identity {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (hq : ∀ i, 0 < q i) (i : Fin m) :
    q i*(∑ j, rationalFlowDecode q F i j*q j) =
      -((∑ j, F i j)-(∑ j, F j i)) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold rationalFlowDecode
  field_simp [ne_of_gt (hq i),ne_of_gt (hq j)]

theorem rational_saturated_flow_completion {m : ℕ} (q t : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) (M ε : ℚ)
    (hq : ∀ i, 0 < q i)
    (hf : RationalSaturatedFlow (fun i => q i*(t i-ε))
      (fun i j => M*q i*q j) F y) :
    ResidualRatConditions q t M ε (rationalFlowDecode q F) := by
  refine ⟨rational_flow_decode_skew q F, rational_flow_decode_bounds q F M hq hf.2.1,?_⟩
  intro i
  have hd := rational_saturated_flow_divergence _ _ F y hf i
  have he := rational_flow_decode_response_identity q F hq i
  have hqi := hq i
  nlinarith

end SparseCompletion
