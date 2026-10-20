/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Material Lean proof authorship: OpenAI Codex.
Classical category-game theorem recalled by Grädel–Leßenich, CSL2012, p.306.
Full-history conventions credit Banach–Mazur source59d4a50 and Choquet source51def6f.
The shrinking closed-ball argument is adapted under Apache-2.0 from source51def6f.
-/
module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.SpecificLimits.Basic
public section
open Set Filter
open scoped Topology
namespace CategoryGame

variable (X : Type u) [TopologicalSpace X]

/-- A legal individual move is any nonempty open set. Equal nested moves are allowed. -/
@[expose] def OpenMove := {U : Set X // IsOpen U ∧ U.Nonempty}

/-- Player I receives the full reverse history of II's moves, including the empty initial history. -/
structure FirstStrategy where
  move : List (OpenMove X) → OpenMove X
  responds : ∀ a h, (move (a :: h)).val ⊆ a.val

/-- Player II receives I's current move and the full reverse history of I's earlier moves. -/
structure SecondStrategy where
  move : OpenMove X → List (OpenMove X) → OpenMove X
  responds : ∀ a h, (move a h).val ⊆ a.val

/-- Earlier opponent moves, most recent first. -/
@[expose] def history (a : ℕ → OpenMove X) : ℕ → List (OpenMove X)
  | 0 => []
  | n + 1 => a n :: history a n

/-- II's moves refine I's responses to their full history. -/
@[expose] def FollowsFirst (σ : FirstStrategy X) (b : ℕ → OpenMove X) : Prop :=
  ∀ n, (b n).val ⊆ (σ.move (history X b n)).val

/-- I's next move refines II's current response. -/
@[expose] def FollowsSecond (τ : SecondStrategy X) (a : ℕ → OpenMove X) : Prop :=
  ∀ n, (a (n + 1)).val ⊆ (τ.move (a n) (history X a n)).val

/-- I wins if every compatible play has one target point in all moves. This is an existential
target-intersection payoff, not the assertion that every point of the intersection lies in A. -/
@[expose] def FirstWins (A : Set X) (σ : FirstStrategy X) : Prop :=
  ∀ b, FollowsFirst X σ b → (A ∩ ⋂ n, (b n).val).Nonempty

/-- II wins if every compatible play has no target point in the common intersection. -/
@[expose] def SecondWins (A : Set X) (τ : SecondStrategy X) : Prop :=
  ∀ a, FollowsSecond X τ a → ¬ (A ∩ ⋂ n, (a n).val).Nonempty

/-- Determinacy means one player has an actual strategy winning against every compatible play. -/
@[expose] def Determined (A : Set X) : Prop :=
  (∃ σ, FirstWins X A σ) ∨ ∃ τ, SecondWins X A τ

variable {X}

@[simp] theorem history_length (a : ℕ → OpenMove X) (n : ℕ) :
    (history X a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

/-- Both players have the same common intersection in a play following I. -/
theorem first_intersection_eq (σ : FirstStrategy X) (b : ℕ → OpenMove X)
    (hb : FollowsFirst X σ b) :
    (⋂ n, (σ.move (history X b n)).val) = ⋂ n, (b n).val := by
  ext x
  simp only [mem_iInter]
  exact ⟨fun h n => σ.responds (b n) (history X b n) (h (n + 1)),
    fun h n => hb n (h n)⟩

/-- Both players have the same common intersection in a play following II. -/
theorem second_intersection_eq (τ : SecondStrategy X) (a : ℕ → OpenMove X)
    (ha : FollowsSecond X τ a) :
    (⋂ n, (a n).val) = ⋂ n, (τ.move (a n) (history X a n)).val := by
  ext x
  simp only [mem_iInter]
  exact ⟨fun h n => ha n (h (n + 1)), fun h n => τ.responds _ _ (h n)⟩

private def jointHistory (σ : FirstStrategy X) (τ : SecondStrategy X) :
    ℕ → List (OpenMove X) × List (OpenMove X)
  | 0 => ([], [])
  | n + 1 =>
    let q := jointHistory σ τ n
    let a := σ.move q.2
    (a :: q.1, τ.move a q.1 :: q.2)

/-- Any two opposing full-history strategies have a jointly compatible infinite play.
An initial move is supplied by I's strategy, so this is not a vacuous compatibility claim. -/
theorem exists_jointPlay (σ : FirstStrategy X) (τ : SecondStrategy X) :
    ∃ a b : ℕ → OpenMove X,
      (∀ n, a n = σ.move (history X b n)) ∧
      (∀ n, b n = τ.move (a n) (history X a n)) ∧
      FollowsFirst X σ b ∧ FollowsSecond X τ a ∧
      ∀ n, (b n).val ⊆ (a n).val ∧ (a (n + 1)).val ⊆ (b n).val := by
  let a := fun n => σ.move (jointHistory σ τ n).2
  let b := fun n => τ.move (a n) (jointHistory σ τ n).1
  have hh (n : ℕ) : (jointHistory σ τ n).1 = history X a n ∧
      (jointHistory σ τ n).2 = history X b n := by
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih => simp only [jointHistory, history, ← ih.1, ← ih.2]; exact ⟨rfl, rfl⟩
  refine ⟨a, b, fun n => congrArg σ.move (hh n).2,
    fun n => congrArg (τ.move (a n)) (hh n).1, ?_, ?_, ?_⟩
  · intro n
    simpa only [a, ← (hh n).2] using τ.responds (a n) (jointHistory σ τ n).1
  · intro n
    simpa only [a, jointHistory, ← (hh n).1] using
      σ.responds (b n) (jointHistory σ τ n).2
  · intro n
    refine ⟨τ.responds _ _, ?_⟩
    simpa only [a, jointHistory] using σ.responds (b n) (jointHistory σ τ n).2

/-- The two players cannot both possess winning strategies for the same target. -/
theorem not_both_winning {A : Set X} (σ : FirstStrategy X) (τ : SecondStrategy X)
    (hσ : FirstWins X A σ) : ¬ SecondWins X A τ := by
  intro hτ
  obtain ⟨a, b, _, _, hb, ha, hba⟩ := exists_jointPlay σ τ
  obtain ⟨x, hxA, hx⟩ := hσ b hb
  exact hτ a ha ⟨x, hxA, mem_iInter.mpr fun n => (hba n).1 (mem_iInter.mp hx n)⟩

/-- A residual set contains a countable intersection of open dense sets, including empty spaces. -/
theorem residual_has_dense_open_sequence {S : Set X} (hS : S ∈ residual X) :
    ∃ D : ℕ → Set X, (∀ n, IsOpen (D n)) ∧ (∀ n, Dense (D n)) ∧ (⋂ n, D n) ⊆ S := by
  classical
  obtain ⟨F, hFo, hFd, hFc, hFS⟩ := mem_residual_iff.mp hS
  let D := enumerateCountable hFc (univ : Set X)
  have hD (n : ℕ) : D n ∈ insert univ F :=
    range_enumerateCountable_subset hFc univ (mem_range_self n)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro n; rcases mem_insert_iff.mp (hD n) with h | h
    · simp [h]
    · exact hFo _ h
  · intro n; rcases mem_insert_iff.mp (hD n) with h | h
    · simp [h]
    · exact hFd _ h
  · intro x hx
    apply hFS
    intro U hU
    obtain ⟨n, hn⟩ := subset_range_enumerate hFc univ hU
    exact hn ▸ mem_iInter.mp hx n

/-- Intersecting a nonempty open move with a dense open set remains a legal move. -/
def cut (D : Set X) (ho : IsOpen D) (hd : Dense D) (a : OpenMove X) : OpenMove X :=
  ⟨a.val ∩ D, a.property.1.inter ho, by
    obtain ⟨x, hxD, hxa⟩ := hd.exists_mem_open a.property.1 a.property.2
    exact ⟨x, hxa, hxD⟩⟩

private def avoidanceStrategy (D : ℕ → Set X) (ho : ∀ n, IsOpen (D n))
    (hd : ∀ n, Dense (D n)) : SecondStrategy X where
  move a h := cut (D h.length) (ho _) (hd _) a
  responds _ _ := inter_subset_left

/-- II can avoid any meagre target, without a metric or Baire-space assumption. -/
theorem second_winning_of_isMeagre {A : Set X} (hA : IsMeagre A) :
    ∃ τ : SecondStrategy X, SecondWins X A τ := by
  obtain ⟨D, ho, hd, hD⟩ := residual_has_dense_open_sequence hA
  refine ⟨avoidanceStrategy D ho hd, ?_⟩
  intro a ha ⟨x, hxA, hx⟩
  apply hD (mem_iInter.mpr fun n => ?_) hxA
  have h := ha n (mem_iInter.mp hx (n + 1))
  simpa only [avoidanceStrategy, cut, history_length] using h.2

/-- A nonmeagre set with the property of Baire is residual on some nonempty open region. -/
theorem open_residual_witness {A : Set X} (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ U : OpenMove X, ∃ S : Set X, S ∈ residual X ∧ U.val ∩ S ⊆ A := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hUne : U.Nonempty := by
    by_contra he
    apply hn
    change ∀ᶠ x in residual X, x ∉ A
    filter_upwards [hAU.mem_iff] with x hx
    exact fun hxa => he ⟨x, hx.mp hxa⟩
  refine ⟨⟨U, hU, hUne⟩, {x | x ∈ A ↔ x ∈ U}, hAU.mem_iff, ?_⟩
  exact fun x hx => hx.2.mpr hx.1

end CategoryGame

namespace CategoryGame
open Set Filter Metric
open scoped Topology
variable {X : Type u} [MetricSpace X]

/-- A positive-radius closed trap of diameter tending to zero fits inside any legal open move. -/
theorem exists_metric_shrink (n : ℕ) (a : OpenMove X) :
    ∃ c : X, ∃ r : ℝ, 0 < r ∧ r ≤ (1 / 2 : ℝ) ^ n ∧ closedBall c r ⊆ a.val := by
  obtain ⟨c, hc⟩ := a.property.2
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (a.property.1.mem_nhds hc)
  refine ⟨c, min r ((1 / 2 : ℝ) ^ n), lt_min hr (pow_pos (by norm_num) _),
    min_le_right _ _, ?_⟩
  exact (closedBall_subset_closedBall (min_le_left _ _)).trans hball

@[expose] noncomputable def metricShrink (n : ℕ) (a : OpenMove X) : X × ℝ :=
  ((exists_metric_shrink n a).choose, (exists_metric_shrink n a).choose_spec.choose)

theorem metricShrink_spec (n : ℕ) (a : OpenMove X) :
    0 < (metricShrink n a).2 ∧ (metricShrink n a).2 ≤ (1 / 2 : ℝ) ^ n ∧
      closedBall (metricShrink n a).1 (metricShrink n a).2 ⊆ a.val :=
  (exists_metric_shrink n a).choose_spec.choose_spec

private def firstInput (U : OpenMove X) (D : ℕ → Set X) (ho : ∀ n, IsOpen (D n))
    (hd : ∀ n, Dense (D n)) : List (OpenMove X) → OpenMove X
  | [] => cut (D 0) (ho _) (hd _) U
  | a :: h => cut (D (h.length + 1)) (ho _) (hd _) a

private noncomputable def categoryStrategy (U : OpenMove X) (D : ℕ → Set X)
    (ho : ∀ n, IsOpen (D n)) (hd : ∀ n, Dense (D n)) : FirstStrategy X where
  move h := ⟨ball (metricShrink h.length (firstInput U D ho hd h)).1
      (metricShrink h.length (firstInput U D ho hd h)).2,
    isOpen_ball, ⟨_, mem_ball_self (metricShrink_spec _ _).1⟩⟩
  responds _ _ := ball_subset_closedBall.trans
    ((metricShrink_spec _ _).2.2.trans inter_subset_left)

/-- In a complete metric space I can force a point in any prescribed open region and every
member of a countable dense-open family. Closed traps are bounded, not assumed compact. -/
theorem first_winning_of_open_residual [CompleteSpace X] {A : Set X} (U : OpenMove X)
    {S : Set X} (hS : S ∈ residual X) (hSA : U.val ∩ S ⊆ A) :
    ∃ σ : FirstStrategy X, FirstWins X A σ := by
  obtain ⟨D, ho, hd, hD⟩ := residual_has_dense_open_sequence hS
  refine ⟨categoryStrategy U D ho hd, ?_⟩
  intro b hb
  let q := fun n => firstInput U D ho hd (history X b n)
  let c := fun n => (metricShrink n (q n)).1
  let r := fun n => (metricShrink n (q n)).2
  have hpos (n : ℕ) : 0 < r n := (metricShrink_spec n (q n)).1
  have hbound (n : ℕ) : r n ≤ (1 / 2 : ℝ) ^ n := (metricShrink_spec n (q n)).2.1
  have hinside (n : ℕ) : closedBall (c n) (r n) ⊆ (q n).val :=
    (metricShrink_spec n (q n)).2.2
  have hnext (n : ℕ) : closedBall (c (n + 1)) (r (n + 1)) ⊆ (b n).val :=
    (hinside (n + 1)).trans inter_subset_left
  have htrap (n : ℕ) : closedBall (c (n + 1)) (r (n + 1)) ⊆ ball (c n) (r n) := by
    have h := (hnext n).trans (hb n)
    simpa only [categoryStrategy, history_length, c, r, q] using h
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
  obtain ⟨x, hx⟩ := Metric.nonempty_iInter_of_nonempty_biInter
    (fun _ => isClosed_closedBall) (fun _ => isBounded_closedBall) hfinite hdiam
  have hq (n : ℕ) : x ∈ (q n).val := hinside n (mem_iInter.mp hx n)
  have hxU : x ∈ U.val := (hq 0).1
  have hxD (n : ℕ) : x ∈ D n := by
    cases n with
    | zero => exact (hq 0).2
    | succ n => simpa only [q, history, firstInput, cut, history_length] using (hq (n + 1)).2
  exact ⟨x, hSA ⟨hxU, hD (mem_iInter.mpr hxD)⟩,
    mem_iInter.mpr fun n => hnext n (mem_iInter.mp hx (n + 1))⟩

/-- On complete metric spaces, a nonmeagre Baire-property target gives I a winning strategy. -/
theorem first_winning_of_nonmeagre [CompleteSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ σ : FirstStrategy X, FirstWins X A σ := by
  obtain ⟨U, S, hS, hSA⟩ := open_residual_witness hA hn
  exact first_winning_of_open_residual U hS hSA

/-- Classical Banach–Mazur determinacy for Baire-property targets, without separability or
absence-of-isolated-points assumptions. This does not assert determinacy for arbitrary targets. -/
theorem determined_of_baireMeasurable [CompleteSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) : Determined X A := by
  by_cases hm : IsMeagre A
  · exact Or.inr (second_winning_of_isMeagre hm)
  · exact Or.inl (first_winning_of_nonmeagre hA hm)

/-- I wins exactly for nonmeagre targets among the Baire-property sets of a complete metric space. -/
theorem first_winning_iff_nonmeagre [CompleteSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) :
    (∃ σ : FirstStrategy X, FirstWins X A σ) ↔ ¬ IsMeagre A := by
  refine ⟨?_, first_winning_of_nonmeagre hA⟩
  rintro ⟨σ, hσ⟩ hm
  obtain ⟨τ, hτ⟩ := second_winning_of_isMeagre hm
  exact not_both_winning σ τ hσ hτ

/-- II wins exactly for meagre targets among the Baire-property sets of a complete metric space. -/
theorem second_winning_iff_isMeagre [CompleteSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) :
    (∃ τ : SecondStrategy X, SecondWins X A τ) ↔ IsMeagre A := by
  refine ⟨?_, second_winning_of_isMeagre⟩
  rintro ⟨τ, hτ⟩
  by_contra hn
  obtain ⟨σ, hσ⟩ := first_winning_of_nonmeagre hA hn
  exact not_both_winning σ τ hσ hτ

end CategoryGame
