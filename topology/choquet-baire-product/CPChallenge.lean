/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Material Lean proof authorship: OpenAI Codex.
Classical Baire-times-alpha-favorable product theorem, recalled by
Li–Zsilinszky1702.06197v3, printed p.2, citing H.E.White1975.
The two maximal-disjoint/dense-refinement helpers are reused under Apache-2.0
from locally-compact-baire d972b3cb0637c0e962c04384f16ec2b3e033d768,
also retained in Banach–Mazur source59d4a50df466480e88ab71bc1f3527bfe0bf1811.
The original White proof was not consulted.
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.SpecificLimits.Basic

public section
open Set
namespace ChoquetProduct

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


variable (Y : Type v) [TopologicalSpace Y]

/-- Individual moves are arbitrary nonempty open sets. -/
@[expose] def OpenMove := {U : Set Y // IsOpen U ∧ U.Nonempty}

/-- A deterministic second-player strategy receives the current first-player
move and the full earlier opponent history, most recent first. -/
structure SecondStrategy where
  move : OpenMove Y → List (OpenMove Y) → OpenMove Y
  responds : ∀ a h, (move a h).val ⊆ a.val

/-- Earlier first-player moves, in reverse chronological order. -/
@[expose] def history (a : ℕ → OpenMove Y) : ℕ → List (OpenMove Y)
  | 0 => []
  | n + 1 => a n :: history a n

/-- A play is compatible when each next first-player move refines the
strategy's response to the current move and its complete prior history. -/
@[expose] def Follows (σ : SecondStrategy Y) (a : ℕ → OpenMove Y) : Prop :=
  ∀ n, (a (n + 1)).val ⊆ (σ.move (a n) (history Y a n)).val

/-- The second player wins every compatible infinite play. -/
@[expose] def SecondWins (σ : SecondStrategy Y) : Prop :=
  ∀ a, Follows Y σ a → (⋂ n, (σ.move (a n) (history Y a n)).val).Nonempty

/-- Banach–Mazur alpha-favorability. This agrees with the usual Choquet
property on nonempty spaces; on the empty space its quantified plays are
absent, an explicit extension rather than a claim of a legal empty-space play. -/
@[expose] def AlphaFavorable : Prop := ∃ σ : SecondStrategy Y, SecondWins Y σ

variable {Y}

@[simp] theorem history_length (a : ℕ → OpenMove Y) (n : ℕ) :
    (history Y a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

/-- Both players have the same payoff intersection in a compatible play. -/
theorem follows_intersection_eq (σ : SecondStrategy Y) (a : ℕ → OpenMove Y)
    (ha : Follows Y σ a) :
    (⋂ n, (a n).val) = ⋂ n, (σ.move (a n) (history Y a n)).val := by
  ext y
  simp only [mem_iInter]
  exact ⟨fun h n => ha n (h (n + 1)), fun h n => σ.responds _ _ (h n)⟩

private def passiveState (σ : SecondStrategy Y) (a₀ : OpenMove Y) :
    ℕ → OpenMove Y × List (OpenMove Y)
  | 0 => (a₀, [])
  | n + 1 => (σ.move (passiveState σ a₀ n).1 (passiveState σ a₀ n).2,
      (passiveState σ a₀ n).1 :: (passiveState σ a₀ n).2)

/-- From every legal initial move there is a compatible play: the first
player can repeat each prescribed response. -/
theorem exists_compatiblePlay (σ : SecondStrategy Y) (a₀ : OpenMove Y) :
    ∃ a : ℕ → OpenMove Y, a 0 = a₀ ∧ Follows Y σ a := by
  let a := fun n => (passiveState σ a₀ n).1
  have hh : ∀ n, (passiveState σ a₀ n).2 = history Y a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change a n :: (passiveState σ a₀ n).2 = a n :: history Y a n; rw [ih]
  refine ⟨a, rfl, fun n => ?_⟩
  change (σ.move (a n) (passiveState σ a₀ n).2).val ⊆ _
  rw [hh]

/-- The empty-space extension is vacuous because no legal first move exists. -/
theorem alphaFavorable_of_isEmpty [IsEmpty Y] : AlphaFavorable Y := by
  refine ⟨⟨fun a _ => a, fun _ _ => subset_rfl⟩, ?_⟩
  intro a _
  obtain ⟨y, _⟩ := (a 0).property.2
  exact isEmptyElim y

variable {X : Type u} [TopologicalSpace X]

private structure Node (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] where
  U : OpenMove X
  a : OpenMove Y
  past : List (OpenMove Y)

private structure Family (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] where
  members : Set (Node X Y)
  disjoint : members.PairwiseDisjoint (fun r => r.U.val)

private def Family.domain (F : Family X Y) : Set X := ⋃ r ∈ F.members, r.U.val

private theorem Family.domain_open (F : Family X Y) : IsOpen F.domain :=
  isOpen_iUnion fun r => isOpen_iUnion fun _ => r.U.property.1

private def Child (σ : SecondStrategy Y) (F : Family X Y) (D : Set (X × Y))
    (r : Node X Y) : Prop :=
  ∃ p ∈ F.members, r.U.val ⊆ p.U.val ∧ r.past = p.a :: p.past ∧
    r.a.val ⊆ (σ.move p.a p.past).val ∧ r.U.val ×ˢ r.a.val ⊆ D

private theorem exists_child (σ : SecondStrategy Y) (F : Family X Y)
    {D : Set (X × Y)} (hDo : IsOpen D) (hDd : Dense D)
    {W : Set X} (hWo : IsOpen W) (hWn : W.Nonempty) (hWG : W ⊆ F.domain) :
    ∃ r, Child σ F D r ∧ r.U.val ⊆ W := by
  obtain ⟨x, hxW⟩ := hWn
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hWG hxW)
  have hAo : IsOpen (W ∩ p.U.val) := hWo.inter p.U.property.1
  have hAn : (W ∩ p.U.val).Nonempty := ⟨x, hxW, hxp⟩
  let V := σ.move p.a p.past
  obtain ⟨⟨a, b⟩, habR, habD⟩ := hDd.inter_open_nonempty _
    (hAo.prod V.property.1) (hAn.prod V.property.2)
  obtain ⟨A, B, hAo', hBo, haA, hbB, hAB⟩ :=
    isOpen_prod_iff.mp (hDo.inter (hAo.prod V.property.1)) a b ⟨habD, habR⟩
  have hAW : A ⊆ W ∩ p.U.val := fun a' ha' => (hAB (show (a', b) ∈ A ×ˢ B from ⟨ha', hbB⟩)).2.1
  have hBV : B ⊆ V.val := fun b' hb' => (hAB (show (a, b') ∈ A ×ˢ B from ⟨haA, hb'⟩)).2.2
  refine ⟨⟨⟨A, hAo', ⟨a, haA⟩⟩, ⟨B, hBo, ⟨b, hbB⟩⟩, p.a :: p.past⟩,
    ⟨p, hp, hAW.trans inter_subset_right, rfl, hBV, fun _ hz => (hAB hz).1⟩,
    hAW.trans inter_subset_left⟩

private theorem refine_family (σ : SecondStrategy Y) (F : Family X Y)
    {D : Set (X × Y)} (hDo : IsOpen D) (hDd : Dense D) :
    ∃ H : Family X Y, (∀ r ∈ H.members, Child σ F D r) ∧
      F.domain ⊆ closure H.domain := by
  obtain ⟨H, hH, hHd, _, hGH⟩ := exists_pairwiseDisjoint_dense_refinement
    (fun r : Node X Y => r.U.val) (Child σ F D) F.domain_open (by
      rintro r ⟨p, hp, hrp, _⟩
      exact ⟨r.U.property.1, r.U.property.2,
        fun _ hx => mem_iUnion₂.mpr ⟨p, hp, hrp hx⟩⟩)
    (fun _ ho hn hG => exists_child σ F hDo hDd ho hn hG)
  exact ⟨⟨H, hHd⟩, hH, hGH⟩

/-- Against a fixed winning second strategy, each countable dense-open
product family has a fiber witness inside a prescribed open region for every
parameter in a dense Gδ set. No entire-section density is asserted. -/
theorem exists_dense_isGdelta_fiber_witness [BaireSpace X]
    (σ : SecondStrategy Y) (hσ : SecondWins Y σ)
    (D : ℕ → Set (X × Y)) (hDo : ∀ n, IsOpen (D n)) (hDd : ∀ n, Dense (D n))
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ ∀ x ∈ G, ∃ y ∈ V, ∀ n, (x, y) ∈ D n := by
  classical
  by_cases hX : Nonempty X
  · let _ : Nonempty X := hX
    let r₀ : Node X Y := ⟨⟨univ, isOpen_univ, univ_nonempty⟩, ⟨V, hVo, hVn⟩, []⟩
    let F₀ : Family X Y := ⟨{r₀}, Set.pairwise_singleton _ _⟩
    choose next hnext using fun n (F : Family X Y) => refine_family σ F (hDo n) (hDd n)
    let F : ℕ → Family X Y := Nat.rec F₀ next
    have hStep (n : ℕ) : (∀ r ∈ (F (n + 1)).members, Child σ (F n) (D n) r) ∧
        (F n).domain ⊆ closure (F (n + 1)).domain := hnext n (F n)
    have hDense (n : ℕ) : Dense (F n).domain := by
      induction n with
      | zero => simp [F, F₀, r₀, Family.domain]
      | succ n ih => exact (ih.mono (hStep n).2).of_closure
    have hG := dense_iInter_of_isOpen_nat (fun n => (F n).domain_open) hDense
    refine ⟨⋂ n, (F n).domain, IsGδ.iInter_of_isOpen (fun n => (F n).domain_open), hG, ?_⟩
    intro x hxG
    choose r hr hxr using fun n => mem_iUnion₂.mp (mem_iInter.mp hxG n)
    have hParent (n : ℕ) :
        (r (n + 1)).past = (r n).a :: (r n).past ∧
        (r (n + 1)).a.val ⊆ (σ.move (r n).a (r n).past).val ∧
        (r (n + 1)).U.val ×ˢ (r (n + 1)).a.val ⊆ D n := by
      obtain ⟨p, hp, hsub, hhist, ha, hrect⟩ := (hStep n).1 _ (hr (n + 1))
      have heq : p = r n := by
        by_contra hne
        exact disjoint_left.mp ((F n).disjoint hp (hr n) hne) (hsub (hxr (n + 1))) (hxr n)
      simpa [heq] using And.intro hhist (And.intro ha hrect)
    have hr₀ : r 0 = r₀ := by simpa [F, F₀] using hr 0
    let a : ℕ → OpenMove Y := fun n => (r n).a
    have hh : ∀ n, (r n).past = history Y a n := by
      intro n
      induction n with
      | zero => rw [hr₀]; rfl
      | succ n ih => rw [(hParent n).1, ih]; rfl
    have ha : Follows Y σ a := by
      intro n
      simpa only [a, ← hh n] using (hParent n).2.1
    obtain ⟨y, hy⟩ := hσ a ha
    have hya (n : ℕ) : y ∈ (r n).a.val :=
      σ.responds _ _ (mem_iInter.mp hy n)
    refine ⟨y, ?_, fun n => (hParent n).2.2 ⟨hxr (n + 1), hya (n + 1)⟩⟩
    simpa only [hr₀] using hya 0
  · have : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨univ, isOpen_univ.isGδ, dense_univ, fun x => isEmptyElim x⟩

/-- The classical Baire-times-alpha-favorable product theorem, for arbitrary
underlying topological spaces, including empty factors. -/
theorem baireSpace_prod [BaireSpace X] (hY : AlphaFavorable Y) : BaireSpace (X × Y) := by
  obtain ⟨σ, hσ⟩ := hY
  constructor
  intro D hDo hDd
  rw [dense_iff_inter_open]
  intro W hWo hWn
  obtain ⟨⟨x₀, y₀⟩, hxy⟩ := hWn
  obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hWo x₀ y₀ hxy
  obtain ⟨G, _, hGd, hG⟩ := exists_dense_isGdelta_fiber_witness σ hσ D hDo hDd hVo ⟨y₀, hyV⟩
  obtain ⟨x, hxU', hxG⟩ := hGd.inter_open_nonempty U hUo ⟨x₀, hxU⟩
  obtain ⟨y, hyV', hyD⟩ := hG x hxG
  exact ⟨(x, y), hUV ⟨hxU', hyV'⟩, mem_iInter.mpr hyD⟩

end ChoquetProduct

namespace ChoquetProduct
open Metric Filter
open scoped Topology

variable {Y : Type v} [MetricSpace Y]

theorem exists_metric_shrink (n : ℕ) (a : OpenMove Y) :
    ∃ c : Y, ∃ r : ℝ, 0 < r ∧ r ≤ (1 / 2 : ℝ) ^ n ∧ closedBall c r ⊆ a.val := by
  obtain ⟨c, hc⟩ := a.property.2
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (a.property.1.mem_nhds hc)
  refine ⟨c, min r ((1 / 2 : ℝ) ^ n), lt_min hr (pow_pos (by norm_num) _),
    min_le_right _ _, ?_⟩
  exact (closedBall_subset_closedBall (min_le_left _ _)).trans hball

@[expose] noncomputable def metricShrink (n : ℕ) (a : OpenMove Y) : Y × ℝ :=
  ((exists_metric_shrink n a).choose, (exists_metric_shrink n a).choose_spec.choose)

theorem metricShrink_spec (n : ℕ) (a : OpenMove Y) :
    0 < (metricShrink n a).2 ∧ (metricShrink n a).2 ≤ (1 / 2 : ℝ) ^ n ∧
      closedBall (metricShrink n a).1 (metricShrink n a).2 ⊆ a.val :=
  (exists_metric_shrink n a).choose_spec.choose_spec

/-- An explicit full-history second strategy with closed traps of radius at
most2^-n. No compactness or local compactness of balls is assumed. -/
@[expose] noncomputable def metricStrategy : SecondStrategy Y where
  move a h := ⟨ball (metricShrink h.length a).1 (metricShrink h.length a).2,
    isOpen_ball, ⟨_, mem_ball_self (metricShrink_spec h.length a).1⟩⟩
  responds a h := ball_subset_closedBall.trans (metricShrink_spec h.length a).2.2

/-- Completeness makes the shrinking closed traps converge, and the next
trap is inside the preceding open response, so the common point is a win. -/
theorem metricStrategy_wins [CompleteSpace Y] : SecondWins Y (metricStrategy (Y := Y)) := by
  intro a ha
  let c : ℕ → Y := fun n => (metricShrink n (a n)).1
  let r : ℕ → ℝ := fun n => (metricShrink n (a n)).2
  have hpos (n : ℕ) : 0 < r n := (metricShrink_spec n (a n)).1
  have hbound (n : ℕ) : r n ≤ (1 / 2 : ℝ) ^ n := (metricShrink_spec n (a n)).2.1
  have htrap (n : ℕ) : closedBall (c (n + 1)) (r (n + 1)) ⊆ ball (c n) (r n) := by
    have hs := (metricShrink_spec (n + 1) (a (n + 1))).2.2
    have h := hs.trans (ha n)
    simpa only [metricStrategy, history_length, c, r] using h
  have hanti (n : ℕ) : closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
    (htrap n).trans ball_subset_closedBall
  have hall {n m : ℕ} (hnm : n ≤ m) : closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact (hanti m).trans ih
  have hfinite (N : ℕ) : (⋂ n ≤ N, closedBall (c n) (r n)).Nonempty := by
    refine ⟨c N, mem_iInter.mpr fun n => mem_iInter.mpr fun hn => ?_⟩
    exact hall hn (mem_closedBall_self (hpos N).le)
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  have hdiam : Tendsto (fun n => diam (closedBall (c n) (r n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => diam_nonneg) (fun n => ?_) hlim
    exact (diam_closedBall (hpos n).le).trans (mul_le_mul_of_nonneg_left (hbound n) (by norm_num))
  obtain ⟨y, hy⟩ := Metric.nonempty_iInter_of_nonempty_biInter
    (fun _ => isClosed_closedBall) (fun _ => isBounded_closedBall) hfinite hdiam
  refine ⟨y, mem_iInter.mpr fun n => ?_⟩
  have h := htrap n (mem_iInter.mp hy (n + 1))
  simpa only [metricStrategy, history_length, c, r] using h

/-- Complete metric spaces have an actual winning second strategy. -/
theorem alphaFavorable_of_completeMetric [CompleteSpace Y] : AlphaFavorable Y :=
  ⟨metricStrategy, metricStrategy_wins⟩

/-- A Baire first factor times an arbitrary complete metric second factor
is Baire; the first factor needs no metric or separation hypotheses. -/
theorem baireSpace_prod_completeMetric {X : Type u} [TopologicalSpace X]
    [BaireSpace X] [CompleteSpace Y] : BaireSpace (X × Y) :=
  baireSpace_prod alphaFavorable_of_completeMetric

end ChoquetProduct
