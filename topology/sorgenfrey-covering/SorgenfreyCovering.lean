/-
Copyright (c) 2026 Arthur Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Ramos
-/
module

public import SorgenfreyDefinitions
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology Cardinal SorgenfreyLine

namespace Counterexample.SorgenfreyLine

/-- A family of right half-open intervals, one at each point of an arbitrary subset,
has a countable subfamily covering that subset. -/
theorem countable_Ico_cover (A : Set ℝₗ) (b : A → ℝₗ)
    (hb : ∀ x : A, x.1 < b x) :
    ∃ T : Set A, T.Countable ∧ ∀ x : A, ∃ y ∈ T, x.1 ∈ Ico y.1 (b y) := by
  classical
  let V : A → Set ℝ := fun x => Ioo (toReal x.1) (toReal (b x))
  obtain ⟨T, hT, hVT⟩ := isOpen_iUnion_countable V (fun _ => isOpen_Ioo)
  let E : Set A := {x | toReal x.1 ∉ ⋃ y, V y}
  have hq : ∀ x : E, ∃ q : ℚ, toReal x.1.1 < q ∧ (q : ℝ) < toReal (b x.1) := by
    intro x
    exact exists_rat_btwn (hb x.1)
  choose q hq₁ hq₂ using hq
  have hqi : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply toReal.injective
    apply le_antisymm
    · by_contra h
      have hlt : toReal y.1.1 < toReal x.1.1 := lt_of_not_ge h
      have hx : toReal x.1.1 ∈ V y.1 :=
        ⟨hlt, (hq₁ x).trans (by simpa [hxy] using hq₂ y)⟩
      exact x.2 (mem_iUnion.2 ⟨y.1, hx⟩)
    · by_contra h
      have hlt : toReal x.1.1 < toReal y.1.1 := lt_of_not_ge h
      have hy : toReal y.1.1 ∈ V x.1 :=
        ⟨hlt, (hq₁ y).trans (by simpa [hxy] using hq₂ x)⟩
      exact y.2 (mem_iUnion.2 ⟨x.1, hy⟩)
  have hE : E.Countable := by
    have : Countable E := Function.Injective.countable hqi
    exact Set.to_countable E
  refine ⟨T ∪ E, hT.union hE, fun x => ?_⟩
  by_cases hx : x ∈ E
  · exact ⟨x, Or.inr hx, left_mem_Ico.2 (hb x)⟩
  · have hxV : toReal x.1 ∈ ⋃ y ∈ T, V y := by
      rw [hVT]
      exact Classical.not_not.mp hx
    rcases mem_iUnion.1 hxV with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyT, hxy⟩
    exact ⟨y, Or.inl hyT, hxy.1.le, hxy.2⟩

/-- Every subset of the Sorgenfrey line is Lindelöf. -/
theorem isLindelof_set (A : Set ℝₗ) : IsLindelof A := by
  classical
  apply isLindelof_of_countable_subcover
  intro ι U hU hcover
  have h : ∀ x : A, ∃ i : ι, ∃ b > x.1, Ico x.1 b ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover x.2)
    obtain ⟨b, hb, hsub⟩ := isOpen_iff.1 (hU i) x.1 hi
    exact ⟨i, b, hb, hsub⟩
  choose i b hb hsub using h
  obtain ⟨T, hT, hc⟩ := countable_Ico_cover A b hb
  refine ⟨i '' T, hT.image i, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hc ⟨x, hx⟩
  exact mem_iUnion.2 ⟨i y, mem_iUnion.2 ⟨mem_image_of_mem i hy, hsub y hxy⟩⟩

instance instHereditarilyLindelofSpace : HereditarilyLindelofSpace ℝₗ :=
  ⟨fun A _ => isLindelof_set A⟩

/-- Disjointification of a countable clopen cover is a locally finite clopen partition. -/
theorem disjointify_clopen_cover {X : Type*} [TopologicalSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClopen (C n)) (hcover : ⋃ n, C n = univ) :
    ∃ D : ℕ → Set X, (∀ n, IsClopen (D n)) ∧ (⋃ n, D n = univ) ∧
      Pairwise (fun m n => Disjoint (D m) (D n)) ∧ LocallyFinite D ∧ ∀ n, D n ⊆ C n := by
  classical
  let D : ℕ → Set X := fun n => C n \ ⋃ k ∈ Finset.range n, C k
  have hD : ∀ n, IsClopen (D n) := fun n =>
    (hC n).diff (isClopen_biUnion_finset (fun k _ => hC k))
  have hc : ⋃ n, D n = univ := by
    apply iUnion_eq_univ_iff.2
    intro x
    have hx : ∃ n, x ∈ C n := iUnion_eq_univ_iff.1 hcover x
    refine ⟨Nat.find hx, Nat.find_spec hx, ?_⟩
    intro h
    rcases mem_iUnion.1 h with ⟨k, hk⟩
    rcases mem_iUnion.1 hk with ⟨hkn, hxk⟩
    exact Nat.find_min hx (Finset.mem_range.1 hkn) hxk
  have hd : Pairwise (fun m n => Disjoint (D m) (D n)) := by
    intro m n hmn
    apply disjoint_left.2
    intro x hxm hxn
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · exact hxn.2 (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨Finset.mem_range.2 hlt, hxm.1⟩⟩)
    · exact hxm.2 (mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨Finset.mem_range.2 hlt, hxn.1⟩⟩)
  have hf : LocallyFinite D := by
    intro x
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.1 hc x
    refine ⟨D n, (hD n).2.mem_nhds hn, (finite_singleton n).subset ?_⟩
    intro m hm
    apply mem_singleton_iff.2
    by_contra hmn
    obtain ⟨y, hym, hyn⟩ := hm
    exact (hd hmn).le_bot ⟨hym, hyn⟩
  exact ⟨D, hD, hc, hd, hf, fun n => diff_subset⟩

/-- Every open cover of every subspace admits a countable pairwise disjoint clopen
refinement. The refinement also is locally finite. -/
theorem clopen_refinement (A : Set ℝₗ) {ι : Type*} (U : ι → Set A)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ) :
    ∃ (β : Type) (_ : Countable β) (D : β → Set A),
      (∀ j, IsClopen (D j)) ∧ (⋃ j, D j = univ) ∧
        Pairwise (fun j k => Disjoint (D j) (D k)) ∧ LocallyFinite D ∧
          ∀ j, ∃ i, D j ⊆ U i := by
  classical
  by_cases hA : Nonempty A
  · letI := hA
    have h : ∀ x : A, ∃ i : ι, ∃ b > x.1,
        (Subtype.val ⁻¹' Ico x.1 b : Set A) ⊆ U i := by
      intro x
      obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.1 hcover x
      obtain ⟨V, hV, hVi⟩ := isOpen_induced_iff.1 (hU i)
      have hxV : x.1 ∈ V := by rw [← hVi] at hi; exact hi
      obtain ⟨b, hb, hsub⟩ := isOpen_iff.1 hV x.1 hxV
      refine ⟨i, b, hb, fun y hy => ?_⟩
      rw [← hVi]
      exact hsub hy
    choose i b hb hsub using h
    let C : A → Set A := fun x => Subtype.val ⁻¹' Ico x.1 (b x)
    have hC : ∀ x, IsClopen (C x) := fun x =>
      (isClopen_Ico x.1 (b x)).preimage continuous_subtype_val
    have hc : (univ : Set A) ⊆ ⋃ x, C x := fun x _ =>
      mem_iUnion.2 ⟨x, left_mem_Ico.2 (hb x)⟩
    haveI : LindelofSpace A := isLindelof_iff_lindelofSpace.1 (isLindelof_set A)
    obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover C (fun x => (hC x).2) hc
    obtain ⟨D, hD, hdcover, hdisj, hfinite, hDC⟩ :=
      disjointify_clopen_cover (C ∘ f) (fun n => hC (f n)) (univ_subset_iff.1 hf)
    exact ⟨ℕ, inferInstance, D, hD, hdcover, hdisj, hfinite,
      fun n => ⟨i (f n), (hDC n).trans (hsub (f n))⟩⟩
  · haveI : IsEmpty A := not_nonempty_iff.1 hA
    refine ⟨Empty, inferInstance, Empty.elim, (fun j => j.elim), ?_,
      (fun j => j.elim), locallyFinite_of_finite _, (fun j => j.elim)⟩
    exact Set.eq_univ_of_forall fun x => isEmptyElim x

/-- Every subspace of the Sorgenfrey line is paracompact. -/
instance instParacompactSpace_subspace (A : Set ℝₗ) : ParacompactSpace A where
  locallyFinite_refinement ι U hU hcover := by
    obtain ⟨β, _, D, hD, hc, _, hf, hsub⟩ := clopen_refinement A U hU hcover
    exact ⟨β, D, fun j => (hD j).2, hc, hf, hsub⟩

instance instParacompactSpace : ParacompactSpace ℝₗ :=
  (Homeomorph.Set.univ ℝₗ).paracompactSpace_iff.1 inferInstance

/-- The Sorgenfrey plane is not Lindelöf: its closed discrete antidiagonal is uncountable. -/
theorem not_lindelofSpace_prod : ¬ LindelofSpace (ℝₗ × ℝₗ) := by
  intro h
  letI := h
  have hc : ({x : ℝₗ × ℝₗ | x.1 + x.2 = 0} : Set (ℝₗ × ℝₗ)).Countable :=
    (isClosed_antidiagonal 0).isLindelof.countable inferInstance
  have hcard := Cardinal.mk_le_aleph0_iff.2 hc.to_subtype
  rw [cardinal_antidiagonal] at hcard
  exact Cardinal.aleph0_lt_continuum.not_ge hcard

/-- The Sorgenfrey plane is not paracompact, since a paracompact Hausdorff space is normal. -/
theorem not_paracompactSpace_prod : ¬ ParacompactSpace (ℝₗ × ℝₗ) := by
  intro h
  letI := h
  exact not_normalSpace_prod inferInstance


/-- Explicit certificate of hereditary Lindelofness for the comparator. -/
theorem hereditarilyLindelofSpace : HereditarilyLindelofSpace ℝₗ := inferInstance

/-- Explicit certificate of paracompactness for every induced subspace. -/
theorem paracompactSpace_subspace (A : Set ℝₗ) : ParacompactSpace A := inferInstance

/-- Explicit certificate of paracompactness of the line. -/
theorem paracompactSpace : ParacompactSpace ℝₗ := inferInstance

end Counterexample.SorgenfreyLine
