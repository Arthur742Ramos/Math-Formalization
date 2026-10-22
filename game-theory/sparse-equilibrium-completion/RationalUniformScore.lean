/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalBinnedOmitted
public import BinnedCompletion
@[expose] public section
namespace SparseCompletion

theorem rational_uniform_score_real {m : ℕ} (hm : 0 < m) (r : ℚ) (j : Fin m) :
    (rationalUniformScore r j : ℝ)=targetScore (uniformTarget m (r : ℝ)) (r : ℝ) j := by
  rw [uniform_target_score]
  unfold rationalUniformScore
  push_cast
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  field_simp [hmR]
  ring

end SparseCompletion
