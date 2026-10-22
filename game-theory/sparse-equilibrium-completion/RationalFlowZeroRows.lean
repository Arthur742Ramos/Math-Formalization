/- AI-assisted formalization under the repository Apache-2.0 license.
Reconstruct zero-weight rows explicitly from a supplied saturated-flow
certificate and the global row guard. Flow existence/search is still separate. -/
module
public import RationalSaturatedFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFlowDecodeWithZeros {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ) (i j : Fin m) : ℚ :=
  if q i=0 then if q j=0 then 0 else -M
  else if q j=0 then M else rationalFlowDecode q F i j

theorem rational_flow_zero_edge {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ)
    (hf : ∀ i j, 0 ≤ F i j ∧ F i j ≤ M*q i*q j)
    (i j : Fin m) (hz : q i=0 ∨ q j=0) : F i j=0 := by
  apply le_antisymm _ (hf i j).1
  calc
    F i j ≤ M*q i*q j := (hf i j).2
    _ = 0 := by
      rcases hz with hi | hj
      · simp only [hi,mul_zero,zero_mul]
      · simp only [hj,mul_zero]

theorem rational_flow_zero_decode_skew {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ) (i j : Fin m) :
    rationalFlowDecodeWithZeros q F M i j= -rationalFlowDecodeWithZeros q F M j i := by
  by_cases hi : q i=0 <;> by_cases hj : q j=0
  · simp [rationalFlowDecodeWithZeros,hi,hj]
  · simp [rationalFlowDecodeWithZeros,hi,hj]
  · simp [rationalFlowDecodeWithZeros,hi,hj]
  · simpa only [rationalFlowDecodeWithZeros,hi,hj,ite_false] using rational_flow_decode_skew q F i j

theorem rational_flow_zero_decode_bounds {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ) (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i)
    (hf : ∀ i j, 0 ≤ F i j ∧ F i j ≤ M*q i*q j) (i j : Fin m) :
    -M ≤ rationalFlowDecodeWithZeros q F M i j ∧ rationalFlowDecodeWithZeros q F M i j ≤ M := by
  by_cases hi : q i=0 <;> by_cases hj : q j=0
  · simp only [rationalFlowDecodeWithZeros,hi,hj,ite_true]
    constructor <;> linarith
  · simp only [rationalFlowDecodeWithZeros,hi,hj,ite_true,ite_false]
    constructor <;> linarith
  · simp only [rationalFlowDecodeWithZeros,hi,hj,ite_true,ite_false]
    constructor <;> linarith
  · simp only [rationalFlowDecodeWithZeros,hi,hj,ite_false,rationalFlowDecode]
    have hqq := mul_pos (lt_of_le_of_ne (hq i) (Ne.symm hi)) (lt_of_le_of_ne (hq j) (Ne.symm hj))
    have hij := hf i j
    have hji := hf j i
    constructor
    · apply (le_div_iff₀ hqq).mpr
      nlinarith
    · apply (div_le_iff₀ hqq).mpr
      nlinarith

theorem rational_flow_zero_decode_supported_response {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M : ℚ)
    (hf : ∀ i j, 0 ≤ F i j ∧ F i j ≤ M*q i*q j)
    (i : Fin m) (hi : q i ≠ 0) :
    q i*(∑ j, rationalFlowDecodeWithZeros q F M i j*q j) =
      -((∑ j, F i j)-(∑ j, F j i)) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : q j=0
  · have hij := rational_flow_zero_edge q F M hf i j (Or.inr hj)
    have hji := rational_flow_zero_edge q F M hf j i (Or.inl hj)
    simp only [rationalFlowDecodeWithZeros,hi,hj,ite_false,ite_true,hij,hji,mul_zero,sub_self,neg_zero]
  · simp only [rationalFlowDecodeWithZeros,hi,hj,ite_false,rationalFlowDecode]
    field_simp [hi,hj]

theorem rational_flow_zero_decode_zero_response {m : ℕ} (q : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (M r : ℚ) (hr : (∑ j, q j)=r)
    (i : Fin m) (hi : q i=0) :
    (∑ j, rationalFlowDecodeWithZeros q F M i j*q j)= -M*r := by
  have hh : ∀ j, rationalFlowDecodeWithZeros q F M i j*q j= -M*q j := by
    intro j
    by_cases hj : q j=0 <;> simp [rationalFlowDecodeWithZeros,hi,hj]
  simp only [hh,← Finset.mul_sum,hr]

theorem rational_saturated_flow_completion_with_zeros {m : ℕ} (q t : Fin m → ℚ)
    (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hr : (∑ j, q j)=r)
    (hg : ∀ i, t i ≤ ε+M*r)
    (hf : RationalSaturatedFlow (fun i => q i*(t i-ε))
      (fun i j => M*q i*q j) F y) :
    ResidualRatConditions q t M ε (rationalFlowDecodeWithZeros q F M) := by
  refine ⟨rational_flow_zero_decode_skew q F M,rational_flow_zero_decode_bounds q F M hM hq hf.2.1,?_⟩
  intro i
  by_cases hi : q i=0
  · rw [rational_flow_zero_decode_zero_response q F M r hr i hi]
    have hh := hg i
    linarith
  · have hd := rational_saturated_flow_divergence _ _ F y hf i
    have he := rational_flow_zero_decode_supported_response q F M hf.2.1 i hi
    have hqi := lt_of_le_of_ne (hq i) (Ne.symm hi)
    nlinarith

end SparseCompletion
