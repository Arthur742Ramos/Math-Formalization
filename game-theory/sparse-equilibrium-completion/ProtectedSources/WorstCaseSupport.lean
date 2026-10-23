/- AI-assisted formalization under the repository Apache-2.0 license.
An attained worst-case operator over actual feasible observation/commitment data.
The finite maximum and minima are noncomputable; no algorithmic cost claim. -/
module
public import ProtectedSources.SupportProblemMinimum
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def zeroExactAnchorInstance (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k) :
    ScaledExactAnchorInstance M k m where
  K := fun _ _ => 0
  D := fun _ _ => 0
  B := fun _ _ => 0
  p := fun h => if h=(⟨0,hk⟩ : Fin k) then 1 else 0
  q := fun _ => 0
  r := 0
  residual_nonnegative := le_refl 0
  anchors_nonnegative := by intro h; split <;> norm_num
  residual_weights_nonnegative := fun _ => le_refl 0
  normalized := by simp
  residual_mass := by simp only [Finset.sum_const_zero]
  core_skew := by intro a b; simp only [neg_zero]
  residual_skew := by intro a b; simp only [neg_zero]
  core_bounds := fun _ _ => ⟨neg_nonpos.mpr hM,hM⟩
  cross_bounds := fun _ _ => ⟨neg_nonpos.mpr hM,hM⟩
  residual_bounds := fun _ _ => ⟨neg_nonpos.mpr hM,hM⟩
  exact_responses := by
    intro a
    cases a <;> simp [response,blockMatrix]

def zeroSupportProblem (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k) (fixed : Bool) :
    AnchoredSupportProblem M k m fixed where
  original := zeroExactAnchorInstance M hM k m hk
  floors := (zeroExactAnchorInstance M hM k m hk).p
  floors_nonnegative := (zeroExactAnchorInstance M hM k m hk).anchors_nonnegative
  floors_original := fun _ => le_refl _
  fixed_original := fun _ => rfl

def supportProblemCounts (M : ℝ) (k m : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : Finset ℕ := by
  classical
  exact (Finset.range (k+m+1)).filter (fun s =>
    ∃ P : AnchoredSupportProblem M k m fixed, supportProblemMinimum P ε hε=s)

theorem supportProblemCounts_nonempty (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    (supportProblemCounts M k m ε hε fixed).Nonempty := by
  classical
  let P := zeroSupportProblem M hM k m hk fixed
  refine ⟨supportProblemMinimum P ε hε,Finset.mem_filter.mpr ⟨?_,⟨P,rfl⟩⟩⟩
  exact Finset.mem_range.mpr (by have hh := supportProblemMinimum_finite P ε hε; omega)

def worstCaseSupport (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  (supportProblemCounts M k m ε hε fixed).max'
    (supportProblemCounts_nonempty M hM k m hk ε hε fixed)

theorem worstCaseSupport_attained (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ P : AnchoredSupportProblem M k m fixed,
      supportProblemMinimum P ε hε=worstCaseSupport M hM k m hk ε hε fixed := by
  classical
  exact (Finset.mem_filter.mp (Finset.max'_mem _
    (supportProblemCounts_nonempty M hM k m hk ε hε fixed))).2

theorem supportProblemMinimum_le_worstCase (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) (P : AnchoredSupportProblem M k m fixed) :
    supportProblemMinimum P ε hε ≤ worstCaseSupport M hM k m hk ε hε fixed := by
  classical
  apply Finset.le_max'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_,⟨P,rfl⟩⟩
  have hh := supportProblemMinimum_finite P ε hε
  omega

theorem worstCaseSupport_finite (M : ℝ) (hM : 0 ≤ M) (k m : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    worstCaseSupport M hM k m hk ε hε fixed ≤ k+m := by
  obtain ⟨P,hP⟩ := worstCaseSupport_attained M hM k m hk ε hε fixed
  rw [←hP]
  exact supportProblemMinimum_finite P ε hε

theorem worstCaseSupport_upper (M : ℝ) (hM : 0 < M) (k m : ℕ) (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (hηM : η ≤ M) (fixed : Bool) :
    (worstCaseSupport M (le_of_lt hM) k m hk η (le_of_lt hη) fixed : ℝ) ≤
      ((2 : ℕ) : ℝ)*min ((k : ℝ)+m) ((k : ℝ)+Real.sqrt (M/η)) := by
  obtain ⟨P,hP⟩ := worstCaseSupport_attained M (le_of_lt hM) k m hk η (le_of_lt hη) fixed
  rw [←hP]
  exact supportProblemMinimum_upper P η hM hη hηM

end
end SparseCompletion
