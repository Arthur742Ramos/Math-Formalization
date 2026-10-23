/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalEvaluation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem rational_interval_system_point {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) :
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x ↔
      RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
        M r ρ η (intervalAux x) := by
  change (∀ row, rationalFormEval
    (rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η row) x ≤
    rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η row) ↔ _
  simp only [RationalIntervalRows,RationalIntervalTailRows,Sum.forall,Prod.forall,
    rationalIntervalCoefficient,rationalIntervalRightSide,Sum.elim_inl,Sum.elim_inr]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,Fin.val_zero,Fin.val_succ]
  simp only [Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false,
    rational_form_eval_add,rational_form_eval_scale,rational_form_eval_sum,
    interval_q_form_eval,interval_v_form_eval,interval_k_form_eval,interval_aux_form_eval]
  unfold RationalIntervalPoint rationalMomentScore
  simp only [rationalFormEval,zero_mul,Finset.sum_const_zero,neg_one_mul,one_mul]
  simp only [and_true,neg_nonpos,neg_le_neg_iff,neg_mul,←sub_eq_add_neg,
    sub_nonpos,sub_nonneg,mul_comm]
  constructor
  · rintro ⟨hq,hm,hV,hK,ha,hlo,hcap,hA,hcall⟩
    refine ⟨hq,le_antisymm hm.1 hm.2,?_,?_,?_,ha,hlo,hcap,?_⟩
    · intro i a
      exact ⟨hV.1 i a,hV.2 i a⟩
    · intro a b
      have hl := hK.1 a b
      have hu := hK.2.1 a b
      linarith
    · intro a b
      exact ⟨hK.2.2.1 a b,hK.2.2.2 a b⟩
    · intro l
      exact ⟨hA.1 l,hA.2 l,hcall l⟩
  · rintro ⟨hq,hm,hV,hK,hKb,ha,hlo,hcap,hA⟩
    refine ⟨hq,⟨le_of_eq hm,le_of_eq hm.symm⟩,⟨?_,?_⟩,⟨?_,?_,?_,?_⟩,ha,hlo,hcap,⟨?_,?_⟩,?_⟩
    · intro i a
      exact (hV i a).1
    · intro i a
      exact (hV i a).2
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      exact (hKb a b).1
    · intro a b
      exact (hKb a b).2
    · intro l
      exact (hA l).1
    · intro l
      exact (hA l).2.1
    · intro l
      exact (hA l).2.2
end SparseCompletion
