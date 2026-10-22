/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ObservationCover

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalClip (lo hi x : ℝ) : ℝ := max lo (min hi x)

def intervalLoss (M lo hi : ℝ) : ℝ := max (M+lo) (M-hi)

theorem interval_clip_bounds (lo hi x : ℝ) (hlu : lo ≤ hi) :
    lo ≤ intervalClip lo hi x ∧ intervalClip lo hi x ≤ hi := by
  unfold intervalClip
  exact ⟨le_max_left _ _,max_le hlu (min_le_left _ _)⟩

theorem interval_clip_neg (lo hi x : ℝ) (hlu : lo ≤ hi) :
    intervalClip (-hi) (-lo) (-x)= -intervalClip lo hi x := by
  unfold intervalClip
  by_cases hxl : x ≤ lo
  · rw [min_eq_left (neg_le_neg hxl),max_eq_right (neg_le_neg hlu),
      min_eq_right (le_trans hxl hlu),max_eq_left hxl]
  · by_cases hxu : hi ≤ x
    · rw [min_eq_right (neg_le_neg (le_trans hlu hxu)),max_eq_left (neg_le_neg hxu),
        min_eq_left hxu,max_eq_right hlu]
    · have hlx : lo ≤ x := le_of_not_ge hxl
      have hxh : x ≤ hi := le_of_not_ge hxu
      rw [min_eq_right (neg_le_neg hlx),max_eq_right (neg_le_neg hxh),
        min_eq_right hxh,max_eq_right hlx]

theorem interval_loss_nonnegative (M lo hi : ℝ) (hlo : -M ≤ lo) :
    0 ≤ intervalLoss M lo hi := by
  exact le_trans (by linarith) (le_max_left _ _)

theorem interval_clip_distance (M lo hi x : ℝ) (hx : -M ≤ x ∧ x ≤ M) (hlu : lo ≤ hi) (hlo : -M ≤ lo) :
    |intervalClip lo hi x-x| ≤ intervalLoss M lo hi := by
  unfold intervalClip intervalLoss
  by_cases hxl : x < lo
  · rw [min_eq_right (le_trans (le_of_lt hxl) hlu),max_eq_left (le_of_lt hxl),abs_of_nonneg (by linarith)]
    exact le_trans (by linarith [hx.1]) (le_max_left _ _)
  · by_cases hxu : hi < x
    · rw [min_eq_left (le_of_lt hxu),max_eq_right hlu,abs_of_nonpos (by linarith)]
      exact le_trans (by linarith [hx.2]) (le_max_right _ _)
    · rw [min_eq_right (le_of_not_gt hxu),max_eq_right (le_of_not_gt hxl),sub_self,abs_zero]
      have h0 : 0 ≤ M+lo := by linarith
      exact le_trans h0 (le_max_left _ _)

def projectedResidual {ι : Type*} (lo hi B : ι → ι → ℝ) : ι → ι → ℝ := by
  classical
  exact fun i j => if i=j then 0 else intervalClip (lo i j) (hi i j) (B i j)

theorem projected_residual_skew {ι : Type*} (lo hi B : ι → ι → ℝ)
    (hB : IsSkew B) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    IsSkew (projectedResidual lo hi B) := by
  intro i j
  by_cases he : i=j
  · subst j
    simp only [projectedResidual,ite_true,neg_zero]
  · simp only [projectedResidual,ite_eq_right he,ite_eq_right (Ne.symm he)]
    rw [(hrev i j he).1,(hrev i j he).2,hB i j,interval_clip_neg _ _ _ (hlu j i (Ne.symm he))]

theorem projected_residual_interval {ι : Type*} (lo hi B : ι → ι → ℝ)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) :
    offDiagonalIntervals lo hi (projectedResidual lo hi B) := by
  intro i j he
  simp only [projectedResidual,ite_eq_right he]
  exact interval_clip_bounds _ _ _ (hlu i j he)

theorem projected_residual_bounds {ι : Type*} (lo hi B : ι → ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j) (hhi : ∀ i j, i ≠ j → hi i j ≤ M) :
    ∀ i j, -M ≤ projectedResidual lo hi B i j ∧ projectedResidual lo hi B i j ≤ M := by
  intro i j
  by_cases he : i=j
  · simp only [projectedResidual,ite_eq_left he]
    exact ⟨by linarith,hM⟩
  · have hh := interval_clip_bounds (lo i j) (hi i j) (B i j) (hlu i j he)
    simp only [projectedResidual,ite_eq_right he]
    exact ⟨le_trans (hlo i j he) hh.1,le_trans hh.2 (hhi i j he)⟩

theorem projected_residual_distance {ι : Type*} (lo hi B : ι → ι → ℝ) (M β : ℝ)
    (hβ : 0 ≤ β) (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β) :
    ∀ i j, |projectedResidual lo hi B i j-B i j| ≤ β := by
  intro i j
  by_cases he : i=j
  · subst j
    have hz : B i i=0 := by linarith [hB i i]
    simp only [projectedResidual,ite_true,hz,sub_self,abs_zero]
    exact hβ
  · simp only [projectedResidual,ite_eq_right he]
    exact le_trans (interval_clip_distance M _ _ _ (hb i j) (hlu i j he) (hlo i j he)) (hloss i j he)

end
end SparseCompletion
