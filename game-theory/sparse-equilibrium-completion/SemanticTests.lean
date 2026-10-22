module
public import SECSolution

public section

open scoped BigOperators
open SparseCompletion

noncomputable section

/-- Cuts ignore zero-mass rows; the separate global guard is necessary even
    for a two-action distribution of total mass one. -/
theorem omitted_row_guard_is_essential :
    let q : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let t : Fin 2 → ℝ := fun i => if i = 0 then 0 else 100
    Cuts 1 1 q t ∧ ¬ ∃ B : Fin 2 → Fin 2 → ℝ,
      (∀ i j, -1 ≤ B i j) ∧ (∀ i, t i + response B q i ≤ 0) := by
  dsimp only
  let q : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let t : Fin 2 → ℝ := fun i => if i = 0 then 0 else 100
  have hq : ∀ i, 0 ≤ q i := by intro i; dsimp [q]; split <;> norm_num
  have hr : ∑ i, q i = 1 := by norm_num [q, Fin.sum_univ_two]
  constructor
  · apply call_bound_implies_cuts q t 1 1 (by norm_num) hq hr
    intro z hz
    simp only [call, Fin.sum_univ_two, q, t]
    norm_num
    unfold envelope
    norm_num
    constructor
    · nlinarith [sq_nonneg (z+1)]
    · positivity
  · rintro ⟨B, hB, hresp⟩
    have hg := response_guard q t B 1 1 0 hq hr hB hresp (1 : Fin 2)
    norm_num [t] at hg
