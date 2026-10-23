/- AI-assisted formalization under the repository Apache-2.0 license.
Finite support search uses the verified rational LP solver. It may be exponential. -/
module
public import ProtectedSources.RationalGapCompression
public import ProtectedSources.RationalAllocationGrid
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSupportMask {m : ℕ} (z : Fin m → Fin 2) : Finset (Fin m) :=
  Finset.univ.filter fun i => (z i).val ≠ 0

def rationalSupportZeros {m : ℕ} (z : Fin m → Fin 2) : RationalLinearSystem (Fin m) m :=
  ⟨fun a i => if (z a).val=0 ∧ i=a then 1 else 0,fun _ => 0⟩

theorem rational_support_zeros_iff {m : ℕ} (z : Fin m → Fin 2) (q : Fin m → ℚ) :
    (rationalSupportZeros z).Satisfies q ↔ ∀ i, (z i).val=0 → q i ≤ 0 := by
  constructor
  · intro h i hi
    have hh := h i
    simpa only [RationalLinearSystem.Satisfies,rationalSupportZeros,hi,true_and,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  · intro h i
    by_cases hi : (z i).val=0
    · simpa only [rationalSupportZeros,hi,true_and,ite_mul,one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h i hi
    · simp only [rationalSupportZeros,hi,false_and,ite_false,zero_mul,
        Finset.sum_const_zero,le_refl]

theorem rational_support_zeros_real {m : ℕ} (z : Fin m → Fin 2) (x : Fin m → ℝ)
    (h : ∀ i, (z i).val=0 → x i=0) : (rationalSupportZeros z).RealSatisfies x := by
  intro a
  by_cases ha : (z a).val=0
  · change (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i) ≤ ((0 : ℚ) : ℝ)
    have he : (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i)=x a := by
      calc
        _ = ∑ i, if i=a then x i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i=a <;> simp [ha,hi]
        _ = _ := by simp
    rw [he,h a ha,Rat.cast_zero]
  · change (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i) ≤ ((0 : ℚ) : ℝ)
    simp only [ha,false_and,ite_false,Rat.cast_zero,zero_mul,Finset.sum_const_zero,le_refl]

theorem rational_support_card_of_zeros {m : ℕ} (z : Fin m → Fin 2) (q : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hz : (rationalSupportZeros z).Satisfies q) :
    (Finset.univ.filter fun i => q i ≠ 0).card ≤ (rationalSupportMask z).card := by
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,?_⟩
  intro he
  exact (Finset.mem_filter.mp hi).2 (le_antisymm
    ((rational_support_zeros_iff z q).mp hz i he) (hq i))

noncomputable def realSupportIndex {m : ℕ} (x : Fin m → ℝ) : Fin m → Fin 2 :=
  fun i => if x i=0 then ⟨0,Nat.zero_lt_succ 1⟩ else ⟨1,Nat.lt_succ_self 1⟩

theorem real_support_index_zero {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (realSupportIndex x i).val=0 ↔ x i=0 := by
  classical
  by_cases hi : x i=0 <;> simp [realSupportIndex,hi]

theorem real_support_index_mask {m : ℕ} (x : Fin m → ℝ) :
    rationalSupportMask (realSupportIndex x)=Finset.univ.filter (fun i => x i ≠ 0) := by
  classical
  ext i
  simp only [rationalSupportMask,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (real_support_index_zero x i)

end SparseCompletion
