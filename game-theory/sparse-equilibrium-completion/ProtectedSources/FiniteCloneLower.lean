/- AI-assisted formalization under the repository Apache-2.0 license.
Actual clone obstruction transported to finite anchor labels and physical minima. -/
module
public import ProtectedSources.FiniteCloneInstance
public import ProtectedSources.WorstCaseSupport
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem finite_clone_physical_to_source (n m : ℕ) (hm : 0 < m) (M η : ℝ)
    (hM : 0 ≤ M) (fixed : Bool) (p : Fin (n+2) → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ)
    (hw : PhysicalAnchoredWitness (finiteScaledCloneInstance n m hm M hM).K
      (finiteScaledCloneInstance n m hm M hM).D (finiteScaledCloneInstance n m hm M hM).p
      M η fixed p q B) :
    ScaledClonedUniformWitness n m M η fixed (fun h => p ((cloneFinEquiv n).symm h)) q B := by
  rcases hw with ⟨hn,hnorm,hfloor,hfixed,hsk,hb,hrows⟩
  let e := cloneFinEquiv n
  refine ⟨fun i => hn (.inr i),?_,?_,?_,?_,?_,?_⟩
  · intro h
    have hh := hfloor (e.symm h)
    change cloneShares n (e (e.symm h)) ≤ p (e.symm h) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · intro hf
    funext h
    rw [hfixed hf]
    change cloneShares n (e (e.symm h))=cloneShares n h
    rw [Equiv.apply_symm_apply]
  · rw [Equiv.sum_comp e.symm p]
    rw [blockWeights_mass] at hnorm
    exact hnorm
  · intro i j
    exact hsk (.inr i) (.inr j)
  · intro i j
    exact hb (.inr i) (.inr j)
  · intro a
    let K := fun a b => M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b
    let D := fun i a => M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a
    have he := response_anchor_pull e K D B (fun h => p (e.symm h)) q
      ((Equiv.sumCongr e (Equiv.refl (Fin m))).symm a)
    simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] at he
    change response (blockMatrix K D B) (blockWeights (fun h => p (e.symm h)) q) a ≤ η
    rw [←he]
    exact hrows _

theorem finite_clone_support_preserved (n m : ℕ)
    (p : Fin (n+2) → ℝ) (q : Fin m → ℝ) :
    (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card =
      (Finset.univ.filter fun a => blockWeights (fun h => p ((cloneFinEquiv n).symm h)) q a ≠ 0).card := by
  classical
  have he := support_anchor_pull (cloneFinEquiv n) (fun h => p ((cloneFinEquiv n).symm h)) q
  simpa only [Equiv.symm_apply_apply] using he

theorem finite_clone_physical_support_lower (n m : ℕ) (hm : 0 < m) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (fixed : Bool) (p : Fin (n+2) → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ)
    (hw : PhysicalAnchoredWitness (finiteScaledCloneInstance n m hm M (le_of_lt hM)).K
      (finiteScaledCloneInstance n m hm M (le_of_lt hM)).D
      (finiteScaledCloneInstance n m hm M (le_of_lt hM)).p M η fixed p q B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
      ((Finset.univ.filter fun a => blockWeights p q a ≠ 0).card : ℝ) := by
  have hs := finite_clone_physical_to_source n m hm M η (le_of_lt hM) fixed p q B hw
  have hl := scaled_cloned_total_support_lower hm M η hM hη fixed _ q B hs
  rw [←finite_clone_support_preserved n m p q] at hl
  exact hl

def finiteCloneSupportProblem (n m : ℕ) (hm : 0 < m) (M : ℝ) (hM : 0 ≤ M) (fixed : Bool) :
    AnchoredSupportProblem M (n+2) m fixed where
  original := finiteScaledCloneInstance n m hm M hM
  floors := (finiteScaledCloneInstance n m hm M hM).p
  floors_nonnegative := (finiteScaledCloneInstance n m hm M hM).anchors_nonnegative
  floors_original := fun _ => le_refl _
  fixed_original := fun _ => rfl

theorem finiteCloneSupportProblem_minimum_lower (n m : ℕ) (hm : 0 < m) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
      (supportProblemMinimum (finiteCloneSupportProblem n m hm M (le_of_lt hM) fixed)
        η (le_of_lt hη) : ℝ) := by
  obtain ⟨p,q,B,hw,hc⟩ := supportProblemMinimum_attained
    (finiteCloneSupportProblem n m hm M (le_of_lt hM) fixed) η (le_of_lt hη)
  have hl := finite_clone_physical_support_lower n m hm M η hM hη fixed p q B hw
  rw [hc] at hl
  exact hl

end
end SparseCompletion
