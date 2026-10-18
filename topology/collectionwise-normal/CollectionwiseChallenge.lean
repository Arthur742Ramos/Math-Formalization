/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Material AI proof contributions: OpenAI Codex, under the user's campaign authorization.
-/
module

public import Mathlib.Topology.Compactness.Paracompact

/-!
# Paracompact expansion and collectionwise separation

The finite-star construction proves Krajewski's paracompact expansion theorem
(1971, Corollary 2.4.1). Closed discrete families are subsequently separated
with pairwise disjoint closures. No cardinal bound on the family is imposed.
-/

public section

open Set Filter Function Topology

universe u v

namespace Collectionwise

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- At every point, a neighborhood meets at most one indexed member.
Repeated nonempty members at distinct indices are therefore disallowed. -/
@[expose] def IsDiscreteFamily (F : ι → Set X) : Prop :=
  ∀ x : X, ∃ N ∈ 𝓝 x, {i | (F i ∩ N).Nonempty}.Subsingleton

/-- The open expansion property, with the index type of the given family. -/
@[expose] def HasOpenExpansion (F : ι → Set X) : Prop :=
  ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧ ∀ i, F i ⊆ U i

/-- Paracompact spaces expand arbitrary locally finite indexed families.
No separation or closedness hypothesis is required. The proof expands by stars
of a locally finite refinement of neighborhoods meeting finitely many members. -/
theorem exists_open_expansion [ParacompactSpace X] {F : ι → Set X}
    (hF : LocallyFinite F) : HasOpenExpansion F := by
  classical
  have hlocal : ∀ x : X, ∃ N : Set X, (x ∈ N ∧ IsOpen N) ∧
      {i | (F i ∩ N).Nonempty}.Finite := fun x =>
    hF.exists_mem_basis (nhds_basis_opens x)
  choose N hNx hNf using hlocal
  rcases precise_refinement N (fun x => (hNx x).2)
      (iUnion_eq_univ_iff.mpr fun x => ⟨x, (hNx x).1⟩) with
    ⟨V, hVo, hVcov, hVf, hVN⟩
  let U : ι → Set X := fun i => ⋃ (x : X) (_ : (F i ∩ V x).Nonempty), V x
  refine ⟨U, fun i => isOpen_iUnion fun x => isOpen_iUnion fun _ => hVo x, ?_, ?_⟩
  · intro z
    rcases hVf z with ⟨W, hzW, hWf⟩
    refine ⟨W, hzW, (hWf.biUnion fun x _ => hNf x).subset ?_⟩
    rintro i ⟨y, hyU, hyW⟩
    rcases mem_iUnion₂.mp hyU with ⟨x, hxF, hyV⟩
    exact mem_iUnion₂.mpr ⟨x, ⟨y, hyV, hyW⟩,
      hxF.mono (inter_subset_inter_right _ (hVN x))⟩
  · intro i y hyF
    rcases iUnion_eq_univ_iff.mp hVcov y with ⟨x, hyV⟩
    exact mem_iUnion₂.mpr ⟨x, ⟨y, hyF, hyV⟩, hyV⟩

theorem IsDiscreteFamily.locallyFinite {F : ι → Set X} (hF : IsDiscreteFamily F) :
    LocallyFinite F := fun x => by
  rcases hF x with ⟨N, hxN, hN⟩
  exact ⟨N, hxN, hN.finite⟩

theorem IsDiscreteFamily.pairwiseDisjoint {F : ι → Set X} (hF : IsDiscreteFamily F) :
    Pairwise (Disjoint on F) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases hF x with ⟨N, hxN, hN⟩
  exact hij (hN ⟨x, hxi, mem_of_mem_nhds hxN⟩ ⟨x, hxj, mem_of_mem_nhds hxN⟩)

/-- Pointwise prescribed open neighborhoods can be respected by closures while
retaining local finiteness. Closedness is essential for the normal shrinking. -/
theorem exists_subordinate_expansion [ParacompactSpace X] [NormalSpace X]
    {F O : ι → Set X} (hF : LocallyFinite F) (hFc : ∀ i, IsClosed (F i))
    (hOo : ∀ i, IsOpen (O i)) (hFO : ∀ i, F i ⊆ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧
      (∀ i, F i ⊆ U i) ∧ ∀ i, closure (U i) ⊆ O i := by
  classical
  rcases exists_open_expansion hF with ⟨W, hWo, hWf, hFW⟩
  choose V hVo hFV hVO using fun i => normal_exists_closure_subset (hFc i) (hOo i) (hFO i)
  refine ⟨fun i => V i ∩ W i, fun i => (hVo i).inter (hWo i),
    hWf.subset (fun _ => inter_subset_right), fun i x hx => ⟨hFV i hx, hFW i hx⟩, ?_⟩
  exact fun i => (closure_mono inter_subset_left).trans (hVO i)

/-- A locally finite family whose closures are pairwise disjoint is discrete.
The neighborhood avoids every closure not containing the given point. -/
theorem discrete_of_locallyFinite_closure_disjoint {U : ι → Set X}
    (hU : LocallyFinite U) (hd : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j)))) :
    IsDiscreteFamily U := by
  intro x
  let N := ⋂ (i : ι) (_ : x ∉ closure (U i)), (closure (U i))ᶜ
  refine ⟨N, hU.closure.iInter_compl_mem_nhds (fun _ => isClosed_closure) x, ?_⟩
  intro i hi j hj
  have hmem : ∀ k, (U k ∩ N).Nonempty → x ∈ closure (U k) := by
    intro k hk
    by_contra hx
    rcases hk with ⟨y, hyU, hyN⟩
    exact (mem_iInter₂.mp hyN k hx) (subset_closure hyU)
  by_contra hij
  exact (hd hij).le_bot ⟨hmem i hi, hmem j hj⟩

/-- For closed indexed families, the neighborhood definition is exactly local
finiteness plus pairwise disjointness, not merely point-finiteness. -/
theorem discrete_closed_iff {F : ι → Set X} (hFc : ∀ i, IsClosed (F i)) :
    IsDiscreteFamily F ↔ LocallyFinite F ∧ Pairwise (Disjoint on F) := by
  constructor
  · exact fun h => ⟨h.locallyFinite, h.pairwiseDisjoint⟩
  · rintro ⟨hf, hd⟩
    apply discrete_of_locallyFinite_closure_disjoint hf
    simpa only [(hFc _).closure_eq] using hd

/-- Every discrete closed indexed family in a paracompact normal space admits
an open expansion with disjoint closures, subordinate to prescribed opens.
In particular this applies to every paracompact Hausdorff space. -/
theorem exists_discrete_expansion [ParacompactSpace X] [NormalSpace X]
    {F O : ι → Set X} (hF : IsDiscreteFamily F) (hFc : ∀ i, IsClosed (F i))
    (hOo : ∀ i, IsOpen (O i)) (hFO : ∀ i, F i ⊆ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧
      (∀ i, F i ⊆ U i) ∧ (∀ i, closure (U i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) ∧ IsDiscreteFamily U := by
  classical
  let T : ι → Set X := fun i => (⋃ (j : ι) (_ : j ≠ i), F j)ᶜ
  have hTo : ∀ i, IsOpen (T i) := by
    intro i
    have hclosed : IsClosed (⋃ j : {j // j ≠ i}, F j) :=
      (hF.locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hFc j)
    simpa only [iUnion_subtype] using hclosed.isOpen_compl
  have hFT : ∀ i, F i ⊆ T i := by
    intro i x hx hbad
    rcases mem_iUnion₂.mp hbad with ⟨j, hji, hxj⟩
    exact (hF.pairwiseDisjoint hji).le_bot ⟨hxj, hx⟩
  rcases exists_subordinate_expansion hF.locallyFinite hFc hTo hFT with
    ⟨V, hVo, hVf, hFV, hVT⟩
  let G : ι → Set X := fun i => V i \ ⋃ (j : ι) (_ : j ≠ i), closure (V j)
  have hGo : ∀ i, IsOpen (G i) := by
    intro i
    have hclosed : IsClosed (⋃ j : {j // j ≠ i}, closure (V j)) :=
      (hVf.closure.comp_injective Subtype.val_injective).isClosed_iUnion
        (fun _ => isClosed_closure)
    exact (hVo i).sdiff (by simpa only [iUnion_subtype] using hclosed)
  have hFG : ∀ i, F i ⊆ G i := by
    intro i x hx
    refine ⟨hFV i hx, ?_⟩
    rintro hbad
    rcases mem_iUnion₂.mp hbad with ⟨j, hji, hxj⟩
    exact hVT j hxj (mem_iUnion₂.mpr ⟨i, Ne.symm hji, hx⟩)
  have hGd : Pairwise (Disjoint on G) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact hxi.2 (mem_iUnion₂.mpr ⟨j, Ne.symm hij, subset_closure hxj.1⟩)
  rcases exists_subordinate_expansion hF.locallyFinite hFc
      (fun i => (hGo i).inter (hOo i)) (fun i x hx => ⟨hFG i hx, hFO i hx⟩) with
    ⟨U, hUo, hUf, hFU, hUG⟩
  have hd : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
    intro i j hij
    exact (hGd hij).mono (fun _ hx => (hUG i hx).1) (fun _ hx => (hUG j hx).1)
  exact ⟨U, hUo, hUf, hFU, fun i x hx => (hUG i hx).2, hd,
    discrete_of_locallyFinite_closure_disjoint hUf hd⟩

/-- Collectionwise normality with explicit indexed closed-family semantics. -/
theorem paracompact_hausdorff_collectionwise [ParacompactSpace X] [T2Space X]
    {F : ι → Set X} (hF : IsDiscreteFamily F) (hFc : ∀ i, IsClosed (F i)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, F i ⊆ U i) ∧
      IsDiscreteFamily U ∧ Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
  rcases exists_discrete_expansion hF hFc (fun _ => isOpen_univ)
      (fun _ => subset_univ _) with ⟨U, ho, _, hFU, _, hd, hf⟩
  exact ⟨U, ho, hFU, hf, hd⟩

end Collectionwise
