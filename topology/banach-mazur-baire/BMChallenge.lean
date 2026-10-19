/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Material Lean proof authorship: OpenAI Codex.
Classical Oxtoby Banach–Mazur characterization; game conventions and recalled
criterion consulted in Li–Zsilinszky (2017), printed pp.2–3.
The maximal-disjoint-refinement helper is reused with attribution from
Arthur742Ramos/Math-Formalization, locally-compact-baire source
 d972b3cb0637c0e962c04384f16ec2b3e033d768 (Apache-2.0).
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.Baire.Lemmas

public section

open Set
namespace BanachMazur

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


variable (X : Type u) [TopologicalSpace X]

/-- Legal individual moves are arbitrary nonempty open sets. -/
@[expose] def OpenMove := {U : Set X // IsOpen U ∧ U.Nonempty}

/-- A full-history first-player strategy. Histories store the opponent's moves
in reverse chronological order. The initial move is `move []`. -/
structure FirstStrategy where
  move : List (OpenMove X) → OpenMove X
  responds : ∀ a h, (move (a :: h)).val ⊆ a.val

/-- The finite history before round `n`, most recent move first. -/
@[expose] def history (a : ℕ → OpenMove X) : ℕ → List (OpenMove X)
  | 0 => []
  | n + 1 => a n :: history a n

/-- Every second-player move refines the first-player move prescribed by the
entire preceding history. The strategy's response law supplies the other half
of the alternating inclusions. -/
@[expose] def Follows (σ : FirstStrategy X) (a : ℕ → OpenMove X) : Prop :=
  ∀ n, (a n).val ⊆ (σ.move (history X a n)).val

/-- The first player wins exactly when every compatible infinite play has
empty intersection. This does not assert that either player must have a
winning strategy. -/
@[expose] def FirstWins (σ : FirstStrategy X) : Prop :=
  ∀ a, Follows X σ a → ¬ (⋂ n, (a n).val).Nonempty

variable {X}

@[simp] theorem history_length (a : ℕ → OpenMove X) (n : ℕ) :
    (history X a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

/-- The two players' intersections agree in every compatible play. -/
theorem follows_intersection_eq (σ : FirstStrategy X) (a : ℕ → OpenMove X)
    (ha : Follows X σ a) :
    (⋂ n, (σ.move (history X a n)).val) = ⋂ n, (a n).val := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx n
    exact σ.responds (a n) (history X a n) (hx (n + 1))
  · intro hx n
    exact ha n (hx n)

private def domain (σ : FirstStrategy X) (F : Set (List (OpenMove X))) : Set X :=
  ⋃ h ∈ F, (σ.move h).val

private theorem domain_open (σ : FirstStrategy X) (F : Set (List (OpenMove X))) :
    IsOpen (domain σ F) :=
  isOpen_iUnion fun h => isOpen_iUnion fun _ => (σ.move h).property.1

private def Child (σ : FirstStrategy X) (F : Set (List (OpenMove X)))
    (h' : List (OpenMove X)) : Prop :=
  ∃ h ∈ F, ∃ a : OpenMove X, h' = a :: h ∧ a.val ⊆ (σ.move h).val

private theorem exists_children (σ : FirstStrategy X) (F : Set (List (OpenMove X))) :
    ∃ F' : Set (List (OpenMove X)), (∀ h ∈ F', Child σ F h) ∧
      F'.PairwiseDisjoint (fun h => (σ.move h).val) ∧
      domain σ F' ⊆ domain σ F ∧ domain σ F ⊆ closure (domain σ F') := by
  apply exists_pairwiseDisjoint_dense_refinement (fun h => (σ.move h).val)
    (Child σ F) (domain_open σ F)
  · intro h' hh'
    obtain ⟨h, hh, a, rfl, has⟩ := hh'
    exact ⟨(σ.move (a :: h)).property.1, (σ.move (a :: h)).property.2,
      fun x hx => mem_iUnion₂.mpr ⟨h, hh, has (σ.responds a h hx)⟩⟩
  · intro W hWo hWn hWG
    obtain ⟨x, hxW⟩ := hWn
    obtain ⟨h, hh, hxh⟩ := mem_iUnion₂.mp (hWG hxW)
    let a : OpenMove X := ⟨W ∩ (σ.move h).val,
      hWo.inter (σ.move h).property.1, ⟨x, hxW, hxh⟩⟩
    refine ⟨a :: h, ⟨h, hh, a, rfl, fun _ hx => hx.2⟩, ?_⟩
    intro y hy
    exact (σ.responds a h hy).1

private noncomputable def nextLevel (σ : FirstStrategy X) (F : Set (List (OpenMove X))) :
    Set (List (OpenMove X)) := Classical.choose (exists_children σ F)

private theorem nextLevel_spec (σ : FirstStrategy X) (F : Set (List (OpenMove X))) :
    (∀ h ∈ nextLevel σ F, Child σ F h) ∧
      (nextLevel σ F).PairwiseDisjoint (fun h => (σ.move h).val) ∧
      domain σ (nextLevel σ F) ⊆ domain σ F ∧
      domain σ F ⊆ closure (domain σ (nextLevel σ F)) :=
  Classical.choose_spec (exists_children σ F)

private noncomputable def levels (σ : FirstStrategy X) : ℕ → Set (List (OpenMove X))
  | 0 => {[]}
  | n + 1 => nextLevel σ (levels σ n)

private theorem level_disjoint (σ : FirstStrategy X) (n : ℕ) :
    (levels σ n).PairwiseDisjoint (fun h => (σ.move h).val) := by
  cases n with
  | zero => exact Set.pairwise_singleton _ _
  | succ n => exact (nextLevel_spec σ (levels σ n)).2.1

private theorem level_subset (σ : FirstStrategy X) (n : ℕ) :
    domain σ (levels σ n) ⊆ (σ.move []).val := by
  induction n with
  | zero => simp [levels, domain]
  | succ n ih => exact (nextLevel_spec σ (levels σ n)).2.2.1.trans ih

private theorem initial_subset_closure_level (σ : FirstStrategy X) (n : ℕ) :
    (σ.move []).val ⊆ closure (domain σ (levels σ n)) := by
  induction n with
  | zero => simpa [levels, domain] using (subset_closure : (σ.move []).val ⊆ closure _)
  | succ n ih =>
    exact ih.trans (closure_minimal (nextLevel_spec σ (levels σ n)).2.2.2 isClosed_closure)

/-- Every full-history first-player strategy on a Baire space has a compatible
play with a common point. No separation, countability or metric hypothesis is
imposed on the space. -/
theorem exists_commonPoint_play [BaireSpace X] (σ : FirstStrategy X) :
    ∃ a : ℕ → OpenMove X, Follows X σ a ∧ (⋂ n, (a n).val).Nonempty := by
  classical
  let U := (σ.move []).val
  have hUo : IsOpen U := (σ.move []).property.1
  let : BaireSpace U := hUo.baireSpace
  let : Nonempty U := let ⟨x, hx⟩ := (σ.move []).property.2; ⟨⟨x, hx⟩⟩
  let D : ℕ → Set U := fun n => Subtype.val ⁻¹' domain σ (levels σ n)
  have hDo : ∀ n, IsOpen (D n) := fun n => (domain_open σ _).preimage continuous_subtype_val
  have hDd : ∀ n, Dense (D n) := by
    intro n
    apply Subtype.dense_iff.mpr
    have himage : Subtype.val '' D n = domain σ (levels σ n) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, level_subset σ n hx⟩, hx, rfl⟩
    rw [himage]
    exact initial_subset_closure_level σ n
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen_nat hDo hDd).nonempty
  have hnodes : ∀ n, ∃ h ∈ levels σ n, x.val ∈ (σ.move h).val := by
    intro n
    obtain ⟨h, hh, hxh⟩ := mem_iUnion₂.mp (mem_iInter.mp hx n)
    exact ⟨h, hh, hxh⟩
  choose nodes hmem hpoint using hnodes
  have hzero : nodes 0 = [] := by simpa [levels] using hmem 0
  have hsuccessors : ∀ n, ∃ a : OpenMove X,
      nodes (n + 1) = a :: nodes n ∧ a.val ⊆ (σ.move (nodes n)).val := by
    intro n
    obtain ⟨h, hh, a, hnext, has⟩ := (nextLevel_spec σ (levels σ n)).1 _ (hmem (n + 1))
    have hxparent : x.val ∈ (σ.move h).val := has (σ.responds a h (hnext ▸ hpoint (n + 1)))
    have heq : h = nodes n := by
      by_contra hne
      exact disjoint_left.mp (level_disjoint σ n hh (hmem n) hne) hxparent (hpoint n)
    exact ⟨a, heq ▸ hnext, heq ▸ has⟩
  choose a ha hsub using hsuccessors
  have hhistory : ∀ n, nodes n = history X a n := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih => rw [ha n, ih]; rfl
  refine ⟨a, ?_, ?_⟩
  · intro n
    simpa only [← hhistory n] using hsub n
  · refine ⟨x.val, mem_iInter.mpr fun n => ?_⟩
    exact σ.responds (a n) (nodes n) ((ha n) ▸ hpoint (n + 1))

private def passiveHistory (σ : FirstStrategy X) : ℕ → List (OpenMove X)
  | 0 => []
  | n + 1 => σ.move (passiveHistory σ n) :: passiveHistory σ n

/-- A strategy always admits a legal infinite play: the opponent may repeat
the prescribed first-player open set. Thus winning is not vacuous because of
an absence of compatible plays. -/
theorem exists_compatiblePlay (σ : FirstStrategy X) :
    ∃ a : ℕ → OpenMove X, Follows X σ a := by
  let a : ℕ → OpenMove X := fun n => σ.move (passiveHistory σ n)
  have hh : ∀ n, passiveHistory σ n = history X a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [passiveHistory, history, ← ih]; rfl
  refine ⟨a, fun n => ?_⟩
  change (σ.move (passiveHistory σ n)).val ⊆ (σ.move (history X a n)).val
  rw [hh n]

/-- On a Baire space, no first-player full-history strategy is winning. -/
theorem not_firstWins_of_baireSpace [BaireSpace X] (σ : FirstStrategy X) :
    ¬ FirstWins X σ := by
  obtain ⟨a, ha, hne⟩ := exists_commonPoint_play σ
  exact fun hw => hw a ha hne

private noncomputable def denseCut (D : ℕ → Set X) (hDo : ∀ n, IsOpen (D n))
    (hDd : ∀ n, Dense (D n)) (n : ℕ) (a : OpenMove X) : OpenMove X :=
  ⟨a.val ∩ D n, a.property.1.inter (hDo n),
    (hDd n).inter_open_nonempty a.val a.property.1 a.property.2⟩

private noncomputable def avoidingStrategy (U : OpenMove X)
    (D : ℕ → Set X) (hDo : ∀ n, IsOpen (D n)) (hDd : ∀ n, Dense (D n)) :
    FirstStrategy X where
  move h := match h with
    | [] => U
    | a :: tail => denseCut D hDo hDd tail.length a
  responds _ _ := inter_subset_left

/-- Failure of Baireness supplies a genuine winning strategy. It starts in
an open set missing a dense-open intersection and cuts into the next dense
open set at every later round. -/
theorem exists_firstWins_of_not_baireSpace (hX : ¬ BaireSpace X) :
    ∃ σ : FirstStrategy X, FirstWins X σ := by
  classical
  have hbad : ∃ D : ℕ → Set X, (∀ n, IsOpen (D n)) ∧
      (∀ n, Dense (D n)) ∧ ¬ Dense (⋂ n, D n) := by
    by_contra! h
    exact hX ⟨h⟩
  obtain ⟨D, hDo, hDd, hnot⟩ := hbad
  rw [dense_iff_inter_open] at hnot
  push Not at hnot
  obtain ⟨U, hUo, hUne, hmiss⟩ := hnot
  let σ := avoidingStrategy (⟨U, hUo, hUne⟩ : OpenMove X) D hDo hDd
  refine ⟨σ, ?_⟩
  intro a ha hcommon
  obtain ⟨x, hx⟩ := hcommon
  have hxU : x ∈ U := ha 0 (mem_iInter.mp hx 0)
  have hxD : ∀ n, x ∈ D n := by
    intro n
    have hnext := ha (n + 1) (mem_iInter.mp hx (n + 1))
    change x ∈ (a n).val ∩ D (history X a n).length at hnext
    simpa only [history_length] using hnext.2
  have hxmiss : x ∈ U ∩ ⋂ n, D n := ⟨hxU, mem_iInter.mpr hxD⟩
  rw [hmiss] at hxmiss
  exact hxmiss

/-- Oxtoby's Banach–Mazur characterization, for arbitrary topological spaces.
The right side says every first-player strategy can be defeated; it does not
assert that one second-player strategy defeats all first-player strategies. -/
theorem baireSpace_iff_no_firstWins :
    BaireSpace X ↔ ∀ σ : FirstStrategy X, ¬ FirstWins X σ := by
  constructor
  · intro hX
    let : BaireSpace X := hX
    exact not_firstWins_of_baireSpace
  · intro h
    by_contra hX
    obtain ⟨σ, hσ⟩ := exists_firstWins_of_not_baireSpace hX
    exact h σ hσ

/-- The empty space has no initial legal move and hence no first-player
strategy. The characterization therefore includes this boundary case without
pretending that an empty space has a legal play. -/
theorem isEmpty_firstStrategy [IsEmpty X] : IsEmpty (FirstStrategy X) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨x, _⟩ := (σ.move []).property.2
  exact isEmptyElim x

end BanachMazur
