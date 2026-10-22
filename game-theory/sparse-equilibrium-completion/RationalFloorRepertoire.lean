/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalParameters
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalResidualFloors {k m : ℕ} (t : Fin m → ℚ) :
    RationalLinearSystem (Fin m) (m+(m*k+(k*k+0*m))) :=
  ⟨fun i => rationalFormScale (-1) (intervalQForm k m 0 i),fun i => -t i⟩

theorem rational_residual_floors_iff {k m : ℕ} (t : Fin m → ℚ)
    (x : Fin (m+(m*k+(k*k+0*m))) → ℚ) :
    (rationalResidualFloors (k := k) t).Satisfies x ↔ ∀ i,t i ≤ intervalQ x i := by
  change (∀ i,rationalFormEval (rationalFormScale (-1) (intervalQForm k m 0 i)) x ≤ -t i) ↔ _
  simp only [rational_form_eval_scale,interval_q_form_eval,neg_one_mul,neg_le_neg_iff]

theorem rational_residual_floors_real_iff {k m : ℕ} (t : Fin m → ℚ)
    (x : Fin (m+(m*k+(k*k+0*m))) → ℝ) :
    (rationalResidualFloors (k := k) t).RealSatisfies x ↔ ∀ i,(t i : ℝ) ≤ intervalQ x i := by
  change (∀ i,rationalFormRealEval (rationalFormScale (-1) (intervalQForm k m 0 i)) x ≤ (-t i : ℚ)) ↔ _
  simp only [rational_form_real_eval_scale,interval_q_real_form_eval,Rat.cast_neg,Rat.cast_one,
    neg_one_mul,neg_le_neg_iff]

theorem rational_residual_floors_real_pack {k m : ℕ} (t : Fin m → ℚ)
    (q : Fin m → ℝ) (V : Fin m → Fin k → ℝ) (K : Fin k → Fin k → ℝ) :
    (rationalResidualFloors t).RealSatisfies (intervalPack q V K (H := 0) Fin.elim0) ↔
      ∀ i,(t i : ℝ) ≤ q i := by
  rw [rational_residual_floors_real_iff,interval_pack_q]

end SparseCompletion
