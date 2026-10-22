/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Developed with substantive OpenAI Codex assistance; no human review claimed.
-/
module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme
public import Mathlib.Order.Disjointed
public import Mathlib.Basic.Denumerable

/-!
# Alexandrov–Urysohn characterization of Baire space

Classical source: Anush Tserunyan, Introduction to descriptive set theory,
Theorem 5.4 and the companion Problem 26 (retained PDF SHA256
b9cf370dee86d3a1fa6f33bf32411f996eb3f7e3e80cac64bd8fb776f601dcd5). Generic scheme limits are from
Felix Weilacher's Mathlib CantorScheme development. The limit, branch-extension
and cylinder-image proofs are adapted from this campaign's OpenBaire package
(frozen source 87652c909a92afded15aad86a901d8c11dd75ed8), with the new
disjoint clopen partition construction supplying injectivity and homeomorphism.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric Topology TopologicalSpace
open scoped ENNReal

namespace BaireCharacterization

/-- Zero-dimensionality is a basis of clopen sets, with no local compactness assumption. -/
def HasClopenBasis (X : Type*) [TopologicalSpace X] : Prop :=
  IsTopologicalBasis {U : Set X | IsClopen U}

/-- Every compact subset has empty interior, including in spaces that are not locally compact. -/
def CompactInteriorEmpty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → interior K = ∅

/-- A countable clopen refinement, before removing repetitions and empty differences. -/
theorem exists_clopen_cover {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    (hB : HasClopenBasis X) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ → Set X, (⋃ n, V n) = U ∧
      ∀ n, IsClopen (V n) ∧ V n ⊆ U ∧ Metric.ediam (V n) ≤ ENNReal.ofReal ε := by
  classical
  have small : ∀ x : U, ∃ V : Set X, IsClopen V ∧ (x : X) ∈ V ∧
      V ⊆ U ∩ ball (x : X) (ε / 2) := by
    intro x
    exact hB.exists_subset_of_mem_open ⟨x.property, mem_ball_self (by positivity)⟩
      (hU.inter isOpen_ball)
  choose V hcl hx hsub using small
  have cover : (⋃ x : U, V x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => (hsub x).trans inter_subset_left
    · intro x hxU
      exact mem_iUnion.mpr ⟨⟨x, hxU⟩, hx _⟩
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable V (fun x => (hcl x).isOpen)
  have hTne : T.Nonempty := by
    obtain ⟨x, hxU⟩ := hne
    rw [← cover, ← hTcover] at hxU
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hxU
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_surjective hTne
  refine ⟨fun n => V (f n).val, ?_, fun n => ⟨hcl _, (hsub _).trans inter_subset_left, ?_⟩⟩
  · apply Eq.trans (b := ⋃ i ∈ T, V i) ?_ (hTcover.trans cover)
    ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨(f n).val, (f n).property, hn⟩
    · rintro ⟨i, hi, hy⟩
      obtain ⟨n, hn⟩ := hf ⟨i, hi⟩
      exact ⟨n, by simpa only [hn] using hy⟩
  · apply Metric.ediam_le_of_forall_dist_le
    intro x hxV y hyV
    have h1 := (hsub (f n).val hxV).2
    have h2 := (hsub (f n).val hyV).2
    have hxy := dist_triangle x ((f n).val : X) y
    rw [dist_comm ((f n).val : X) y] at hxy
    exact (hxy.trans_lt (add_lt_add h1 h2)).le.trans (by linarith)

/-- Every nonempty clopen set has a genuinely infinite small clopen partition.
The compact-interior hypothesis forces a non-total-bounded scale, preventing
a finite family of surviving cells. -/
theorem exists_clopen_partition {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] (hB : HasClopenBasis X) (hK : CompactInteriorEmpty X)
    {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ → Set X, (⋃ n, V n) = U ∧ Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      ∀ n, IsClopen (V n) ∧ (V n).Nonempty ∧ V n ⊆ U ∧
        Metric.ediam (V n) ≤ ENNReal.ofReal ε := by
  classical
  have hnc : ¬ IsCompact U := by
    intro hc
    have he := hK U hc
    rw [hU.isOpen.interior_eq] at he
    exact hne.ne_empty he
  have hnt : ¬ TotallyBounded U := fun ht =>
    hnc (isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hU.isClosed.isComplete⟩)
  rw [Metric.totallyBounded_iff] at hnt
  push Not at hnt
  obtain ⟨δ, hδ, hδcover⟩ := hnt
  let r := min ε (δ / 2)
  have hr : 0 < r := lt_min hε (by positivity)
  obtain ⟨C, hcover, hC⟩ := exists_clopen_cover hB hU.isOpen hne hr
  let D := disjointed C
  have hDcover : (⋃ n, D n) = U := iUnion_disjointed.trans hcover
  have hDcl : ∀ n, IsClopen (D n) := fun n =>
    disjointedRec (fun _ i ht => ht.diff (hC i).1) (hC n).1
  let J := {n : ℕ // (D n).Nonempty}
  let point : J → X := fun j => j.property.choose
  have hpoint : ∀ j : J, point j ∈ D j.val := fun j => j.property.choose_spec
  have hJinf : Infinite J := by
    by_contra hf
    let : Finite J := not_infinite_iff_finite.mp hf
    apply hδcover (range point) (finite_range point)
    intro x hxU
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hDcover ▸ hxU)
    let j : J := ⟨n, x, hn⟩
    refine mem_iUnion₂.mpr ⟨point j, mem_range_self j, ?_⟩
    have he : edist x (point j) ≤ ENNReal.ofReal r :=
      (Metric.edist_le_ediam_of_mem hn (hpoint j)).trans
        ((Metric.ediam_mono (disjointed_subset C n)).trans (hC n).2.2)
    have hd : dist x (point j) ≤ r := by
      rw [edist_dist] at he
      exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp he
    exact hd.trans_lt (lt_of_le_of_lt (min_le_right ε (δ / 2)) (by linarith))
  let := hJinf
  let e : ℕ ≃ J := Classical.choice (inferInstance : Nonempty (ℕ ≃ J))
  refine ⟨fun n => D (e n).val, ?_, ?_, fun n => ⟨hDcl _, (e n).property,
    (disjointed_subset C _).trans (hC _).2.1, ?_⟩⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun n => (disjointed_subset C _).trans (hC _).2.1
    · intro x hxU
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDcover ▸ hxU)
      obtain ⟨k, hk⟩ := e.surjective (⟨n, x, hn⟩ : J)
      exact mem_iUnion.mpr ⟨k, by simpa only [hk] using hn⟩
  · intro i j hij
    apply disjoint_disjointed C
    intro he
    exact hij (e.injective (Subtype.ext he))
  · exact ((Metric.ediam_mono (disjointed_subset C _)).trans (hC _).2.2).trans
      (ENNReal.ofReal_le_ofReal (min_le_left _ _))

/-- A countably branching clopen scheme, with children covering each parent,
nested closures and geometric diameter control. Lists use `PiNat.res`'s
reverse-prefix convention, so a child has the form `a :: l`. -/
structure ClopenScheme (X : Type*) [MetricSpace X] where
  sets : List ℕ → Set X
  root : sets [] = univ
  isClopen : ∀ l, IsClopen (sets l)
  nonempty : ∀ l, (sets l).Nonempty
  closure_child : ∀ l a, closure (sets (a :: l)) ⊆ sets l
  disjoint : CantorScheme.Disjoint sets
  cover : ∀ l, (⋃ a, sets (a :: l)) = sets l
  diameter : ∀ l a, Metric.ediam (sets (a :: l)) ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (l.length + 1))

/-- Full infinite branching with clopen, nonempty, disjoint shrinking children. -/
theorem exists_clopen_scheme (X : Type*) [MetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [Nonempty X]
    (hB : HasClopenBasis X) (hK : CompactInteriorEmpty X) : Nonempty (ClopenScheme X) := by
  classical
  let P := {U : Set X // IsClopen U ∧ U.Nonempty}
  have step := fun (U : P) (n : ℕ) =>
    exists_clopen_partition hB hK U.property.1 U.property.2
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  choose V hcover hdisj hprops using step
  let D : List ℕ → P := fun l => by
    induction l with
    | nil => exact ⟨univ, isClopen_univ, ⟨Classical.arbitrary X, mem_univ _⟩⟩
    | cons a l ih => exact ⟨V ih (l.length + 1) a,
        (hprops ih (l.length + 1) a).1, (hprops ih (l.length + 1) a).2.1⟩
  refine ⟨{
    sets := fun l => (D l).val
    root := rfl
    isClopen := fun l => (D l).property.1
    nonempty := fun l => (D l).property.2
    closure_child := ?_
    disjoint := fun l => hdisj (D l) (l.length + 1)
    cover := fun l => hcover (D l) (l.length + 1)
    diameter := fun l a => (hprops (D l) (l.length + 1) a).2.2.2 }⟩
  intro l a
  rw [((hprops (D l) (l.length + 1) a).1).isClosed.closure_eq]
  exact (hprops (D l) (l.length + 1) a).2.2.1

namespace ClopenScheme
variable {X : Type*} [MetricSpace X] (S : ClopenScheme X)

theorem isOpen (l : List ℕ) : IsOpen (S.sets l) := (S.isClopen l).isOpen

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
nested clopen sets; the upstream construction chooses this point. -/
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
one prescribed point in every later clopen set. -/
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

/-- Disjoint siblings make distinct branches have distinct limits. -/
theorem injective_limit [CompleteSpace X] : Injective S.limit := by
  intro x y h
  have he := S.disjoint.map_injective h
  exact congrArg Subtype.val he

/-- The branch-limit bijection is a homeomorphism, including inverse continuity. -/
def homeomorph [CompleteSpace X] : (ℕ → ℕ) ≃ₜ X :=
  (Equiv.ofBijective S.limit ⟨S.injective_limit, S.surjective_limit⟩).toHomeomorphOfContinuousOpen
    S.continuous_limit S.isOpenMap_limit

end ClopenScheme

/-- Alexandrov–Urysohn sufficiency with a supplied complete metric. -/
theorem nonempty_homeomorph_of_completeSpace (X : Type*) [MetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [Nonempty X]
    (hB : HasClopenBasis X) (hK : CompactInteriorEmpty X) : Nonempty (X ≃ₜ (ℕ → ℕ)) := by
  let S := Classical.choice (exists_clopen_scheme X hB hK)
  exact ⟨S.homeomorph.symm⟩

/-- Classical sufficiency, independent of the choice of compatible complete metric. -/
theorem nonempty_homeomorph (X : Type*) [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    (hB : HasClopenBasis X) (hK : CompactInteriorEmpty X) : Nonempty (X ≃ₜ (ℕ → ℕ)) := by
  let := upgradeIsCompletelyMetrizable X
  exact nonempty_homeomorph_of_completeSpace X hB hK

/-- Baire cylinders are both open and closed in the product topology. -/
theorem isClopen_cylinder (x : ℕ → ℕ) (n : ℕ) : IsClopen (PiNat.cylinder x n) := by
  refine ⟨?_, PiNat.isOpen_cylinder _ x n⟩
  change IsClosed {y : ℕ → ℕ | ∀ i, i < n → y i = x i}
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

/-- The standard Baire space has a clopen basis. -/
theorem baire_hasClopenBasis : HasClopenBasis (ℕ → ℕ) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.isOpen
  · intro x U hx hU
    obtain ⟨V, ⟨y, n, rfl⟩, hxV, hVU⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hx hU
    exact ⟨PiNat.cylinder y n, isClopen_cylinder y n, hxV, hVU⟩

/-- A compact Baire subset cannot contain a cylinder: its coordinate images are finite. -/
theorem baire_compactInteriorEmpty : CompactInteriorEmpty (ℕ → ℕ) := by
  intro K hK
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨V, ⟨y, n, rfl⟩, _, hVK⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hx isOpen_interior
  have hf := (hK.image (continuous_apply n)).finite_of_discrete
  obtain ⟨k, hk⟩ := hf.exists_notMem
  apply hk
  refine ⟨Function.update y n k, interior_subset (hVK (PiNat.update_mem_cylinder y n k)), ?_⟩
  simp

/-- Pullback of the literal clopen-basis property through a homeomorphism. -/
theorem HasClopenBasis.of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hB : HasClopenBasis Y) (e : X ≃ₜ Y) : HasClopenBasis X := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.isOpen
  · intro x U hx hU
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open
      (mem_image_of_mem e hx) (e.isOpenMap U hU)
    refine ⟨e ⁻¹' V, hV.preimage e.continuous, hxV, ?_⟩
    intro z hz
    obtain ⟨w, hw, he⟩ := hVU hz
    exact e.injective he ▸ hw

/-- Pullback of empty compact interiors through a homeomorphism. -/
theorem CompactInteriorEmpty.of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hK : CompactInteriorEmpty Y) (e : X ≃ₜ Y) : CompactInteriorEmpty X := by
  intro K hc
  have he := hK (e '' K) (hc.image e.continuous)
  rw [← e.image_interior] at he
  exact image_eq_empty.mp he

/-- Full Alexandrov–Urysohn characterization, with all four properties explicit. -/
theorem nonempty_homeomorph_iff (X : Type*) [TopologicalSpace X] :
    Nonempty (X ≃ₜ (ℕ → ℕ)) ↔ Nonempty X ∧ PolishSpace X ∧
      HasClopenBasis X ∧ CompactInteriorEmpty X := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv.nonempty, e.isClosedEmbedding.polishSpace,
      baire_hasClopenBasis.of_homeomorph e, baire_compactInteriorEmpty.of_homeomorph e⟩
  · rintro ⟨hne, hp, hB, hK⟩
    let := hne
    let := hp
    exact nonempty_homeomorph X hB hK

end BaireCharacterization

