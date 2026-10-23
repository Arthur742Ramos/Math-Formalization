/- Classical finite-moment recombination, using Mathlib's Caratheodory theorem.
   Follow-on development for sparse equilibrium completion.
   AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.SparseCompletion
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open scoped BigOperators
open Set

namespace SparseCompletion
noncomputable section

def pushWeights {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (i : ι) : ℝ :=
  ∑ j, if label j = i then w j else 0

theorem pushWeights_nonneg {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∀ i, 0 ≤ pushWeights label w i := by
  intro i
  exact Finset.sum_nonneg fun j _ => by
    split
    · exact hw j
    · exact le_rfl

theorem pushWeights_mass {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) : ∑ i, pushWeights label w i = ∑ j, w j := by
  simp only [pushWeights]
  rw [Finset.sum_comm]
  simp

theorem pushWeights_moment {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (f : ι → ℝ) :
    (∑ i, pushWeights label w i*f i) = ∑ j, w j*f (label j) := by
  simp only [pushWeights, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

theorem pushWeights_zero_outside {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (s : Finset ι) (hs : ∀ j, label j ∈ s)
    (i : ι) (hi : i ∉ s) : pushWeights label w i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : label j ≠ i := by intro he; exact hi (he ▸ hs j)
  simp only [ite_eq_right hj]

theorem pushWeights_support_card {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) :
    (Finset.univ.filter fun i => pushWeights label w i ≠ 0).card ≤ Fintype.card κ := by
  classical
  apply le_trans (Finset.card_le_card (show
    Finset.univ.filter (fun i => pushWeights label w i ≠ 0) ⊆ Finset.univ.image label from ?_))
    (le_trans (Finset.card_image_le) (by simp))
  intro i hi
  have hne := (Finset.mem_filter.mp hi).2
  by_contra hn
  apply hne
  apply Finset.sum_eq_zero
  intro j _
  have hj : label j ≠ i := by
    intro he
    exact hn (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he⟩)
  simp only [ite_eq_right hj]

/-- A finite nonnegative weighted sample can be replaced by at most d+1 of
    its original labels while preserving mass and d real features exactly.
    Classical Caratheodory/Tchakaloff recombination is credited to Mathlib. -/
theorem finite_moment_recombination {ι : Type*} (ν : Type) [Fintype ν] (s : Finset ι)
    (q : ι → ℝ) (F : ι → ν → ℝ) (r : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hr : ∑ i ∈ s, q i = r) (hrpos : 0 < r) :
    ∃ (κ : Type) (_ : Fintype κ) (label : κ → ι) (w : κ → ℝ),
      Function.Injective label ∧ (∀ j, label j ∈ s) ∧
      (∀ j, 0 < w j) ∧ (∑ j, w j = r) ∧
      Fintype.card κ ≤ Fintype.card ν+1 ∧
      (∑ j, w j • F (label j)) = ∑ i ∈ s, q i • F i := by
  classical
  let μ : ν → ℝ := ∑ i ∈ s, (q i/r) • F i
  have hn : ∑ i ∈ s, q i/r = 1 := by
    rw [← Finset.sum_div, hr, div_self (ne_of_gt hrpos)]
  have hμ : μ ∈ convexHull ℝ (F '' (s : Set ι)) := by
    exact (convex_convexHull ℝ (F '' (s : Set ι))).sum_mem (t := s) (z := F)
      (fun i hi => div_nonneg (hq i hi) (le_of_lt hrpos)) hn
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
  obtain ⟨κ, hκ, z, w, hz, hind, hw, hsum, hm⟩ := eq_pos_convex_span_of_mem_convexHull hμ
  let _ : Fintype κ := hκ
  have hlabels : ∀ j, ∃ i, i ∈ s ∧ F i = z j := by
    intro j
    exact hz (mem_range_self j)
  choose label hlabel hfeature using hlabels
  have hinj : Function.Injective label := by
    intro a b hab
    apply hind.injective
    rw [← hfeature a, ← hfeature b, hab]
  refine ⟨κ, hκ, label, fun j => r*w j, hinj, hlabel,
    (fun j => mul_pos hrpos (hw j)), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, hsum, mul_one]
  · have hc := hind.card_le_finrank_succ
    have hdim := Submodule.finrank_le (vectorSpan ℝ (range z))
    have hc' := le_trans hc (Nat.add_le_add_right hdim 1)
    simpa only [Module.finrank_pi] using hc'
  · calc
      _ = r • (∑ j, w j • z j) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_smul, hfeature j]
      _ = r • μ := by rw [hm]
      _ = ∑ i ∈ s, q i • F i := by
        dsimp [μ]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_smul]
        congr 1
        field_simp

theorem finite_feature_compression {ι : Type*} [Fintype ι]
    (ν : Type) [Fintype ν] (q : ι → ℝ) (F : ι → ν → ℝ) (r : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r) (hrpos : 0 < r) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ Fintype.card ν+1 ∧
      ∀ h, (∑ i, q' i*F i h) = ∑ i, q i*F i h := by
  classical
  let s := Finset.univ.filter fun i => q i ≠ 0
  have hs : ∑ i ∈ s, q i = r := by
    simpa only [s, Finset.sum_filter_ne_zero] using hr
  obtain ⟨κ, hκ, label, w, _hinj, hlabel, hw, hmass, hcard, hm⟩ :=
    finite_moment_recombination ν s q F r (fun i _ => hq i) hs hrpos
  let _ : Fintype κ := hκ
  refine ⟨pushWeights label w, pushWeights_nonneg label w (fun j => le_of_lt (hw j)), ?_, ?_, ?_, ?_⟩
  · rw [pushWeights_mass, hmass]
  · intro i hi
    exact pushWeights_zero_outside label w s hlabel i (by simp [s, hi])
  · exact le_trans (pushWeights_support_card label w) hcard
  · intro h
    rw [pushWeights_moment]
    have hh := congrArg (fun f : ν → ℝ => f h) hm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [hh]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hnot
    have hqi : q i = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    rw [hqi, zero_mul]

end
end SparseCompletion
