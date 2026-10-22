/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Developed with substantive OpenAI Codex assistance; no human review claimed.
-/
module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme

/-!
# Open Baire-space representation

The construction follows the classical open-scheme proof in David Marker,
Descriptive Set Theory (Fall 2002), Theorem 1.17. All nonempty hypotheses
are explicit. Generic scheme limits and their continuity are credited to
Felix Weilacher's Mathlib CantorScheme development.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric Topology TopologicalSpace
open scoped ENNReal

namespace OpenBaire

/-- Every nonempty open set has a countable cover by nonempty open sets
of arbitrarily small diameter whose closures remain inside the set. -/
theorem exists_open_refinement {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ → Set X, (⋃ n, V n) = U ∧
      ∀ n, IsOpen (V n) ∧ (V n).Nonempty ∧ closure (V n) ⊆ U ∧
        Metric.ediam (V n) ≤ ENNReal.ofReal ε := by
  classical
  have small : ∀ x : U, ∃ r : ℝ, 0 < r ∧ closure (ball (x : X) r) ⊆ U ∧
      Metric.ediam (ball (x : X) r) ≤ ENNReal.ofReal ε := by
    intro x
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU x x.property
    let r := min (δ / 2) (ε / 2)
    have hr : 0 < r := lt_min (by positivity) (by positivity)
    refine ⟨r, hr, ?_, ?_⟩
    · apply Subset.trans closure_ball_subset_closedBall
      apply Subset.trans (closedBall_subset_ball (by dsimp [r]; linarith [min_le_left (δ/2) (ε/2)])) hsub
    · calc
        Metric.ediam (ball (x : X) r) ≤ ENNReal.ofReal (2 * r) := by
          rw [← Metric.eball_ofReal]
          calc
            Metric.ediam (Metric.eball (x : X) (ENNReal.ofReal r)) ≤
                2 * ENNReal.ofReal r := Metric.ediam_eball_le
            _ = ENNReal.ofReal (2 * r) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by dsimp [r]; linarith [min_le_right (δ/2) (ε/2)])
  choose r hr hcl hd using small
  let B : U → Set X := fun x => ball (x : X) (r x)
  have cover : (⋃ x : U, B x) = U := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp hy
      exact hcl x (subset_closure hx)
    · intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hr _)⟩
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable B (fun _ => isOpen_ball)
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    rw [← cover, ← hTcover] at hx
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hx
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_surjective hTne
  refine ⟨fun n => B (f n).val, ?_, fun n => ⟨isOpen_ball, ?_, hcl _, hd _⟩⟩
  · apply Eq.trans (b := ⋃ i ∈ T, B i) ?_ (hTcover.trans cover)
    ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨(f n).val, (f n).property, hn⟩
    · rintro ⟨i, hi, hy⟩
      obtain ⟨n, hn⟩ := hf ⟨i, hi⟩
      exact ⟨n, by simpa only [hn] using hy⟩
  · exact ⟨_, mem_ball_self (hr _)⟩

/-- A countably branching open scheme, with children covering each parent,
nested closures and geometric diameter control. Lists use `PiNat.res`'s
reverse-prefix convention, so a child has the form `a :: l`. -/
structure OpenScheme (X : Type*) [MetricSpace X] where
  sets : List ℕ → Set X
  root : sets [] = univ
  isOpen : ∀ l, IsOpen (sets l)
  nonempty : ∀ l, (sets l).Nonempty
  closure_child : ∀ l a, closure (sets (a :: l)) ⊆ sets l
  cover : ∀ l, (⋃ a, sets (a :: l)) = sets l
  diameter : ∀ l a, Metric.ediam (sets (a :: l)) ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (l.length + 1))

/-- Construction of a genuine open covering scheme, with no compactness
or absence-of-isolated-points assumption. -/
theorem exists_open_scheme (X : Type*) [MetricSpace X]
    [SecondCountableTopology X] [Nonempty X] : Nonempty (OpenScheme X) := by
  classical
  let P := {U : Set X // IsOpen U ∧ U.Nonempty}
  have step := fun (U : P) (n : ℕ) =>
    exists_open_refinement U.property.1 U.property.2
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  choose V hcover hprops using step
  let D : List ℕ → P := fun l => by
    induction l with
    | nil => exact ⟨univ, isOpen_univ, ⟨Classical.arbitrary X, mem_univ _⟩⟩
    | cons a l ih => exact ⟨V ih (l.length + 1) a,
        (hprops ih (l.length + 1) a).1, (hprops ih (l.length + 1) a).2.1⟩
  refine ⟨{
    sets := fun l => (D l).val
    root := rfl
    isOpen := fun l => (D l).property.1
    nonempty := fun l => (D l).property.2
    closure_child := ?_
    cover := ?_
    diameter := ?_ }⟩
  · intro l a
    exact (hprops (D l) (l.length + 1) a).2.2.1
  · intro l
    exact hcover (D l) (l.length + 1)
  · intro l a
    exact (hprops (D l) (l.length + 1) a).2.2.2

namespace OpenScheme
variable {X : Type*} [MetricSpace X] (S : OpenScheme X)

/-- The geometric level bound gives the upstream vanishing-diameter contract. -/
theorem vanishingDiam : CantorScheme.VanishingDiam S.sets := by
  intro x
  change Tendsto (fun n : ℕ => Metric.ediam (S.sets (PiNat.res x n))) atTop (𝓝 0)
  have hu := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  rw [ENNReal.ofReal_zero] at hu
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hz hu
  · exact Filter.Eventually.of_forall
      (fun n => (bot_le : (0 : ℝ≥0∞) ≤ Metric.ediam (S.sets (PiNat.res x n))))
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  change Metric.ediam (S.sets (x m :: PiNat.res x m)) ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1))
  have h := S.diameter (PiNat.res x m) (x m)
  rw [PiNat.res_length] at h
  exact h

theorem domain_eq_univ [CompleteSpace X] : (CantorScheme.inducedMap S.sets).1 = univ :=
  CantorScheme.ClosureAntitone.map_of_vanishingDiam S.vanishingDiam
    S.closure_child S.nonempty

/-- The limit map is total because each branch has a unique point in the
nested open sets; the upstream construction chooses this point. -/
def limit [CompleteSpace X] (x : ℕ → ℕ) : X :=
  (CantorScheme.inducedMap S.sets).2 ⟨x, by rw [S.domain_eq_univ]; exact mem_univ _⟩

theorem limit_mem [CompleteSpace X] (x : ℕ → ℕ) (n : ℕ) :
    S.limit x ∈ S.sets (PiNat.res x n) :=
  CantorScheme.map_mem _ n

theorem continuous_limit [CompleteSpace X] : Continuous S.limit := by
  apply S.vanishingDiam.map_continuous.comp
  fun_prop

/-- A point carried by every set along a branch is its limit. -/
theorem limit_eq [CompleteSpace X] (x : ℕ → ℕ) {y : X}
    (hy : ∀ n, y ∈ S.sets (PiNat.res x n)) : S.limit x = y := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨n, hn⟩ := S.vanishingDiam.dist_lt ε hε x
  exact (hn _ (S.limit_mem x n) _ (hy n)).le

/-- Covering permits extending any prescribed finite prefix while keeping
one prescribed point in every later open set. -/
theorem exists_branch_through (x : ℕ → ℕ) (n : ℕ) {y : X}
    (hy : y ∈ S.sets (PiNat.res x n)) :
    ∃ z ∈ PiNat.cylinder x n, ∀ k, y ∈ S.sets (PiNat.res z k) := by
  classical
  have child_exists : ∀ l, y ∈ S.sets l → ∃ a, y ∈ S.sets (a :: l) := by
    intro l hl
    exact mem_iUnion.mp (S.cover l ▸ hl)
  let child : List ℕ → ℕ := fun l => if h : y ∈ S.sets l then
    (child_exists l h).choose else 0
  have hchild : ∀ l, y ∈ S.sets l → y ∈ S.sets (child l :: l) := by
    intro l hl
    simpa only [child, dite_eq_left hl] using (child_exists l hl).choose_spec
  let path : ℕ → List ℕ := fun m => Nat.rec (PiNat.res x n)
    (fun _ l => child l :: l) m
  have hpath : ∀ m, y ∈ S.sets (path m) := by
    intro m
    induction m with
    | zero => exact hy
    | succ m ih => exact hchild (path m) ih
  let z : ℕ → ℕ := fun k => if k < n then x k else child (path (k - n))
  have hz : z ∈ PiNat.cylinder x n := by
    intro k hk
    exact ite_eq_left hk
  have hres : ∀ m, PiNat.res z (n + m) = path m := by
    intro m
    induction m with
    | zero =>
      change PiNat.res z (n + 0) = PiNat.res x n
      simpa only [Nat.add_zero] using (PiNat.res_eq_res.mpr hz)
    | succ m ih =>
      rw [Nat.add_succ, PiNat.res_succ, ih]
      change z (n + m) :: path m = child (path m) :: path m
      congr 1
      dsimp [z]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
  refine ⟨z, hz, fun k => ?_⟩
  by_cases hk : n ≤ k
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [hres]
    exact hpath m
  · have hk' : k ≤ n := by omega
    have hanti : Antitone (fun j => S.sets (PiNat.res z j)) := by
      apply antitone_nat_of_succ_le
      intro j
      exact (CantorScheme.ClosureAntitone.antitone S.closure_child) _ _
    apply hanti hk'
    change y ∈ S.sets (PiNat.res z n)
    rw [PiNat.res_eq_res.mpr hz]
    exact hy

/-- Exact cylinder images, the essential strengthening beyond continuous
surjectivity. This equality supplies both openness and surjectivity. -/
theorem image_cylinder [CompleteSpace X] (x : ℕ → ℕ) (n : ℕ) :
    S.limit '' PiNat.cylinder x n = S.sets (PiNat.res x n) := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hres : PiNat.res z n = PiNat.res x n := PiNat.res_eq_res.mpr hz
    rw [← hres]
    exact S.limit_mem z n
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := S.exists_branch_through x n hy
    exact ⟨z, hz, S.limit_eq z hzy⟩

theorem isOpenMap_limit [CompleteSpace X] : IsOpenMap S.limit := by
  apply (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).isOpenMap_iff.mpr
  rintro _ ⟨x, n, rfl⟩
  rw [S.image_cylinder]
  exact S.isOpen _

theorem surjective_limit [CompleteSpace X] : Surjective S.limit := by
  have h := S.image_cylinder (fun _ => 0) 0
  simp only [PiNat.cylinder_zero, PiNat.res_zero, S.root, image_univ] at h
  exact range_eq_univ.mp h

end OpenScheme

/-- Every nonempty second-countable complete metric space is a continuous
open image of Baire space, with its product topology of discrete naturals. -/
theorem exists_continuous_open_surjective_of_completeSpace (X : Type*)
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [Nonempty X] :
    ∃ f : (ℕ → ℕ) → X, Continuous f ∧ IsOpenMap f ∧ Surjective f := by
  let S := Classical.choice (exists_open_scheme X)
  exact ⟨S.limit, S.continuous_limit, S.isOpenMap_limit, S.surjective_limit⟩

/-- Classical open Baire-space representation of any nonempty Polish space.
No particular complete metric is fixed in the statement. -/
theorem exists_continuous_open_surjective (X : Type*) [TopologicalSpace X]
    [PolishSpace X] [Nonempty X] :
    ∃ f : (ℕ → ℕ) → X, Continuous f ∧ IsOpenMap f ∧ Surjective f := by
  let := upgradeIsCompletelyMetrizable X
  exact exists_continuous_open_surjective_of_completeSpace X

/-- Nonemptiness is necessary as well as sufficient; in particular the empty
Polish space is not an image of the inhabited Baire space. -/
theorem exists_continuous_open_surjective_iff_nonempty (X : Type*)
    [TopologicalSpace X] [PolishSpace X] :
    (∃ f : (ℕ → ℕ) → X, Continuous f ∧ IsOpenMap f ∧ Surjective f) ↔ Nonempty X := by
  constructor
  · rintro ⟨f, _⟩
    exact ⟨f (fun _ => 0)⟩
  · intro h
    let := h
    exact exists_continuous_open_surjective X

end OpenBaire
