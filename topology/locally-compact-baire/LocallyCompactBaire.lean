/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Material Lean proof authorship: OpenAI Codex.
Adapted compact-fiber projection argument: Aarts–Lutzer (1973), Section 4.1,
printed pp.8–9; arbitrary first factor and R1 fiber assumptions are explicit.
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.Baire.LocallyCompactRegular

public section

open Set

namespace LocallyCompactBaire

/-- An arbitrary collection of labelled sets has a maximal pairwise-disjoint
subfamily satisfying any prescribed admissibility predicate. -/
theorem exists_maximal_pairwiseDisjoint_refinement {X : Type u} {α : Type v}
    (f : α → Set X) (P : α → Prop) :
    ∃ F : Set α, (∀ a ∈ F, P a) ∧ F.PairwiseDisjoint f ∧
      ∀ F' : Set α, (∀ a ∈ F', P a) → F'.PairwiseDisjoint f → F ⊆ F' → F' ⊆ F := by
  let S : Set (Set α) := {F | (∀ a ∈ F, P a) ∧ F.PairwiseDisjoint f}
  obtain ⟨F, hF⟩ := zorn_subset S (by
    intro c hcs hc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, ?_⟩
    · rintro a ⟨A, hAc, haA⟩
      exact (hcs hAc).1 a haA
    · rintro a ⟨A, hAc, haA⟩ b ⟨B, hBc, hbB⟩ hab
      obtain rfl | hAB := eq_or_ne A B
      · exact (hcs hAc).2 haA hbB hab
      · rcases hc hAc hBc hAB with hAB | hBA
        · exact (hcs hBc).2 (hAB haA) hbB hab
        · exact (hcs hAc).2 haA (hBA hbB) hab
    · intro A hAc
      exact subset_sUnion_of_mem hAc)
  exact ⟨F, hF.prop.1, hF.prop.2, fun F' hP hdisj hsub => hF.2 ⟨hP, hdisj⟩ hsub⟩

/-- If admissible nonempty open sets refine every nonempty open part of an
open set `G`, a pairwise-disjoint admissible subfamily has union dense in `G`.
The labels and the ambient space may live in independent universes. -/
theorem exists_pairwiseDisjoint_dense_refinement {X : Type u} {α : Type v}
    [TopologicalSpace X] (f : α → Set X) (P : α → Prop) {G : Set X}
    (hG : IsOpen G)
    (hP : ∀ a, P a → IsOpen (f a) ∧ (f a).Nonempty ∧ f a ⊆ G)
    (hrefine : ∀ W : Set X, IsOpen W → W.Nonempty → W ⊆ G →
      ∃ a, P a ∧ f a ⊆ W) :
    ∃ F : Set α, (∀ a ∈ F, P a) ∧ F.PairwiseDisjoint f ∧
      (⋃ a ∈ F, f a) ⊆ G ∧ G ⊆ closure (⋃ a ∈ F, f a) := by
  classical
  obtain ⟨F, hFP, hFd, hmax⟩ := exists_maximal_pairwiseDisjoint_refinement f P
  refine ⟨F, hFP, hFd, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact (hP a (hFP a ha)).2.2 hxa
  · intro x hxG
    by_contra hxcl
    let W : Set X := G \ closure (⋃ a ∈ F, f a)
    have hWo : IsOpen W := hG.sdiff isClosed_closure
    have hWne : W.Nonempty := ⟨x, hxG, hxcl⟩
    obtain ⟨a, haP, haW⟩ := hrefine W hWo hWne (fun _ hx => hx.1)
    have haDisjoint : ∀ b ∈ F, Disjoint (f a) (f b) := by
      intro b hb
      apply disjoint_left.mpr
      intro y hya hyb
      exact (haW hya).2 (subset_closure (mem_iUnion₂.mpr ⟨b, hb, hyb⟩))
    have hInsertP : ∀ b ∈ insert a F, P b := by
      intro b hb
      rcases mem_insert_iff.mp hb with rfl | hb
      · exact haP
      · exact hFP b hb
    have hInsertD : (insert a F).PairwiseDisjoint f :=
      hFd.insert (fun b hb _ => haDisjoint b hb)
    have haF : a ∈ F := hmax (insert a F) hInsertP hInsertD (subset_insert a F)
      (mem_insert a F)
    obtain ⟨y, hy⟩ := (hP a haP).2.1
    exact (disjoint_left.mp (haDisjoint a haF)) hy hy

end LocallyCompactBaire

namespace LocallyCompactBaire

open Set TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private structure RectFamily (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  members : Set (Set X × PositiveCompacts Y)
  opens : ∀ r ∈ members, IsOpen r.1 ∧ r.1.Nonempty
  disjoint : members.PairwiseDisjoint Prod.fst

private def RectFamily.domain (F : RectFamily X Y) : Set X := ⋃ r ∈ F.members, r.1

private theorem RectFamily.domain_open (F : RectFamily X Y) : IsOpen F.domain :=
  isOpen_iUnion fun r => isOpen_iUnion fun hr => (F.opens r hr).1

private def Child (F : RectFamily X Y) (D : Set (X × Y))
    (r : Set X × PositiveCompacts Y) : Prop :=
  IsOpen r.1 ∧ r.1.Nonempty ∧ ∃ p ∈ F.members,
    r.1 ⊆ p.1 ∧ closure (r.2 : Set Y) ⊆ interior (p.2 : Set Y) ∧
    r.1 ×ˢ closure (r.2 : Set Y) ⊆ D

private theorem exists_child [R1Space Y] [LocallyCompactSpace Y]
    (F : RectFamily X Y) {D : Set (X × Y)} (hDo : IsOpen D) (hDd : Dense D)
    {W : Set X} (hWo : IsOpen W) (hWn : W.Nonempty) (hWG : W ⊆ F.domain) :
    ∃ r, Child F D r ∧ r.1 ⊆ W := by
  obtain ⟨x, hxW⟩ := hWn
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hWG hxW)
  have hA : IsOpen (W ∩ p.1) := hWo.inter (F.opens p hp).1
  have hAn : (W ∩ p.1).Nonempty := ⟨x, hxW, hxp⟩
  have hR : IsOpen ((W ∩ p.1) ×ˢ interior (p.2 : Set Y)) := hA.prod isOpen_interior
  obtain ⟨⟨a, b⟩, habR, habD⟩ := hDd.inter_open_nonempty _ hR
    (hAn.prod p.2.interior_nonempty)
  obtain ⟨A, B, hAo, hBo, haA, hbB, hAB⟩ :=
    isOpen_prod_iff.mp (hDo.inter hR) a b ⟨habD, habR⟩
  obtain ⟨K, hK⟩ := hBo.exists_positiveCompacts_closure_subset ⟨b, hbB⟩
  have hAW : A ⊆ W ∩ p.1 := by
    intro a' ha'
    exact (@hAB (a', b) ⟨ha', hbB⟩).2.1
  have hBY : B ⊆ interior (p.2 : Set Y) := by
    intro b' hb'
    exact (@hAB (a, b') ⟨haA, hb'⟩).2.2
  refine ⟨(A, K), ⟨hAo, ⟨a, haA⟩, p, hp, ?_, hK.trans hBY, ?_⟩, ?_⟩
  · exact hAW.trans inter_subset_right
  · intro z hz
    exact (hAB ⟨hz.1, hK hz.2⟩).1
  · exact hAW.trans inter_subset_left

private theorem refine_family [R1Space Y] [LocallyCompactSpace Y]
    (F : RectFamily X Y) {D : Set (X × Y)} (hDo : IsOpen D) (hDd : Dense D) :
    ∃ H : RectFamily X Y, (∀ r ∈ H.members, Child F D r) ∧
      F.domain ⊆ closure H.domain := by
  obtain ⟨H, hH, hHd, _, hGH⟩ := exists_pairwiseDisjoint_dense_refinement
    (X := X) (α := Set X × PositiveCompacts Y) Prod.fst (Child F D)
    F.domain_open (by
      rintro r ⟨hro, hrn, p, hp, hrp, _⟩
      exact ⟨hro, hrn, fun x hx => mem_iUnion₂.mpr ⟨p, hp, hrp hx⟩⟩)
    (fun _ ho hn hG => exists_child F hDo hDd ho hn hG)
  exact ⟨⟨H, fun r hr => ⟨(hH r hr).1, (hH r hr).2.1⟩, hHd⟩, hH, hGH⟩

/-- A countable family of dense open product sets has fiber points in a fixed
nonempty open region of the locally compact R₁ factor, for all parameters
in some dense Gδ set. This asserts fiber existence, not dense entire sections. -/
theorem exists_dense_isGdelta_fiber_witness [BaireSpace X] [R1Space Y]
    [LocallyCompactSpace Y] (D : ℕ → Set (X × Y))
    (hDo : ∀ n, IsOpen (D n)) (hDd : ∀ n, Dense (D n))
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ ∀ x ∈ G, ∃ y ∈ V, ∀ n, (x, y) ∈ D n := by
  classical
  by_cases hX : Nonempty X
  · let _ : Nonempty X := hX
    obtain ⟨K₀, hK₀⟩ := hVo.exists_positiveCompacts_closure_subset hVn
    let F₀ : RectFamily X Y :=
      ⟨{(univ, K₀)}, by simp only [mem_singleton_iff]; rintro r rfl; exact ⟨isOpen_univ, univ_nonempty⟩,
        pairwiseDisjoint_singleton _ _⟩
    choose next hnext using fun n (F : RectFamily X Y) => refine_family F (hDo n) (hDd n)
    let F : ℕ → RectFamily X Y := Nat.rec F₀ next
    have hStep (n : ℕ) : (∀ r ∈ (F (n + 1)).members, Child (F n) (D n) r) ∧
        (F n).domain ⊆ closure (F (n + 1)).domain := hnext n (F n)
    have hDense (n : ℕ) : Dense (F n).domain := by
      induction n with
      | zero => simp [F, F₀, RectFamily.domain]
      | succ n ih => exact (ih.mono (hStep n).2).of_closure
    have hG := dense_iInter_of_isOpen_nat (fun n => (F n).domain_open) hDense
    refine ⟨⋂ n, (F n).domain, IsGδ.iInter_of_isOpen (fun n => (F n).domain_open), hG, ?_⟩
    intro x hxG
    have hxF (n : ℕ) : x ∈ (F n).domain := mem_iInter.mp hxG n
    choose r hr hxr using fun n => mem_iUnion₂.mp (hxF n)
    have hParent (n : ℕ) : closure ((r (n + 1)).2 : Set Y) ⊆ interior ((r n).2 : Set Y) := by
      obtain ⟨_, _, p, hp, hsub, hK, _⟩ := (hStep n).1 _ (hr (n + 1))
      have hxp : x ∈ p.1 := hsub (hxr (n + 1))
      have heq : p = r n := by
        by_contra hne
        exact disjoint_left.mp ((F n).disjoint hp (hr n) hne) hxp (hxr n)
      simpa [heq] using hK
    have hKanti (n : ℕ) : closure ((r (n + 1)).2 : Set Y) ⊆ closure ((r n).2 : Set Y) :=
      (hParent n).trans (interior_subset.trans subset_closure)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => closure ((r n).2 : Set Y)) hKanti
      (fun n => (r n).2.nonempty.closure) (r 0).2.isCompact.closure
      (fun _ => isClosed_closure)
    have hr₀ : r 0 = (univ, K₀) := by simpa [F, F₀] using hr 0
    have hyV' : y ∈ V := hK₀ (by simpa [hr₀] using mem_iInter.mp hy 0)
    refine ⟨y, hyV', ?_⟩
    intro n
    obtain ⟨_, _, _, _, _, _, hrect⟩ := (hStep n).1 _ (hr (n + 1))
    exact hrect ⟨hxr (n + 1), mem_iInter.mp hy (n + 1)⟩
  · have : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨univ, isOpen_univ.isGδ, dense_univ, fun x => isEmptyElim x⟩

/-- The first projection of a dense Gδ product set, restricted to a fixed
nonempty open fiber region, contains a dense Gδ set of parameters. -/
theorem exists_dense_isGdelta_subset_image_fst [BaireSpace X] [R1Space Y]
    [LocallyCompactSpace Y] {D : Set (X × Y)} (hDg : IsGδ D) (hDd : Dense D)
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ G ⊆ Prod.fst '' (D ∩ (univ ×ˢ V)) := by
  obtain ⟨A, hAo, hEq⟩ := hDg.eq_iInter_nat
  have hAd (n : ℕ) : Dense (A n) := hDd.mono (by
    intro z hz
    rw [hEq] at hz
    exact mem_iInter.mp hz n)
  obtain ⟨G, hGg, hGd, hG⟩ := exists_dense_isGdelta_fiber_witness A hAo hAd hVo hVn
  refine ⟨G, hGg, hGd, ?_⟩
  intro x hx
  obtain ⟨y, hyV, hyA⟩ := hG x hx
  refine ⟨(x, y), ⟨?_, trivial, hyV⟩, rfl⟩
  rw [hEq]
  exact mem_iInter.mpr hyA

/-- A Baire space times a locally compact R₁ space is Baire, with no
countable-base, separation or nonemptiness hypothesis on the first factor. -/
theorem baireSpace_prod [BaireSpace X] [R1Space Y] [LocallyCompactSpace Y] :
    BaireSpace (X × Y) := by
  constructor
  intro D hDo hDd
  rw [dense_iff_inter_open]
  intro W hWo hWn
  obtain ⟨⟨x₀, y₀⟩, hxy⟩ := hWn
  obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hWo x₀ y₀ hxy
  obtain ⟨G, _, hGd, hG⟩ := exists_dense_isGdelta_fiber_witness D hDo hDd hVo ⟨y₀, hyV⟩
  obtain ⟨x, hxU', hxG⟩ := hGd.inter_open_nonempty U hUo ⟨x₀, hxU⟩
  obtain ⟨y, hyV', hyD⟩ := hG x hxG
  exact ⟨(x, y), hUV ⟨hxU', hyV'⟩, mem_iInter.mpr hyD⟩

/-- The compact R₁ specialization requires no countability or metrizability. -/
theorem baireSpace_prod_of_compact [BaireSpace X] [R1Space Y] [CompactSpace Y] :
    BaireSpace (X × Y) := baireSpace_prod

end LocallyCompactBaire
