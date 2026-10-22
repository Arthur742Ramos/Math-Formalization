/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalProjection
public import CompletionGeometry

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_clip_endpoint_distance (lo hi lo' hi' x δ : ℝ)
    (hx : lo ≤ x ∧ x ≤ hi) (hlu' : lo' ≤ hi') (hδ : 0 ≤ δ)
    (hl : |lo-lo'| ≤ δ) (hu : |hi-hi'| ≤ δ) :
    |intervalClip lo' hi' x-x| ≤ δ := by
  obtain ⟨hl1,hl2⟩ := abs_le.mp hl
  obtain ⟨hu1,hu2⟩ := abs_le.mp hu
  unfold intervalClip
  by_cases hxl : x < lo'
  · rw [min_eq_right (le_trans (le_of_lt hxl) hlu'),max_eq_left (le_of_lt hxl),
      abs_of_nonneg (by linarith)]
    linarith [hx.1]
  · by_cases hxu : hi' < x
    · rw [min_eq_left (le_of_lt hxu),max_eq_right hlu',abs_of_nonpos (by linarith)]
      linarith [hx.2]
    · rw [min_eq_right (le_of_not_gt hxu),max_eq_right (le_of_not_gt hxl),sub_self,abs_zero]
      exact hδ

theorem interval_system_projection_distance {ν : Type*} (lo hi lo' hi' A : ν → ν → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : IsSkew A) (hI : offDiagonalIntervals lo hi A)
    (hlu' : ∀ i j, i ≠ j → lo' i j ≤ hi' i j)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    ∀ i j, |A i j-projectedResidual lo' hi' A i j| ≤ δ := by
  intro i j
  by_cases he : i=j
  · subst j
    have hz : A i i=0 := by have h := hA i i; linarith
    simp only [projectedResidual,ite_true,hz,sub_self,abs_zero]
    exact hδ
  · simp only [projectedResidual,ite_eq_right he]
    rw [abs_sub_comm]
    exact interval_clip_endpoint_distance _ _ _ _ _ _ (hI i j he) (hlu' i j he) hδ
      (hd i j he).1 (hd i j he).2

def exploitability {ν : Type*} [Fintype ν] [Nonempty ν] (A : ν → ν → ℝ) (x : ν → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (response A x)

theorem exploitability_le_iff {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (v : ℝ) :
    exploitability A x ≤ v ↔ ∀ i, response A x i ≤ v := by
  unfold exploitability
  simp only [Finset.sup'_le_iff,Finset.mem_univ,true_implies]

theorem response_le_exploitability {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (i : ν) : response A x i ≤ exploitability A x :=
  Finset.le_sup' (response A x) (Finset.mem_univ i)

theorem exploitability_perturbation {ν : Type*} [Fintype ν] [Nonempty ν]
    (A B : ν → ν → ℝ) (x : ν → ℝ) (δ r : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=r) (hAB : ∀ i j, |A i j-B i j| ≤ δ) :
    |exploitability A x-exploitability B x| ≤ δ*r := by
  apply abs_le.mpr
  constructor
  · have h : exploitability B x ≤ exploitability A x+δ*r := by
      apply (exploitability_le_iff B x _).mpr
      intro i
      have hp := (abs_le.mp (response_perturbation A B x δ r hx hm hAB i)).1
      linarith [response_le_exploitability A x i]
    linarith
  · have h : exploitability A x ≤ exploitability B x+δ*r := by
      apply (exploitability_le_iff A x _).mpr
      intro i
      have hp := (abs_le.mp (response_perturbation A B x δ r hx hm hAB i)).2
      linarith [response_le_exploitability B x i]
    linarith

theorem exploitability_continuous {ν : Type*} [Fintype ν] [Nonempty ν] :
    Continuous (fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2) := by
  unfold exploitability
  apply Continuous.finset_sup'_apply
  intro i _
  unfold response
  fun_prop

end
end SparseCompletion
