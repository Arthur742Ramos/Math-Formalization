/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
Material Lean proof authorship: OpenAI Codex.
Strategy lifting follows Dorais–Mummert, arXiv:0907.4126v2, Proposition 3.2.
Polish image conclusion: Chen, Notes on quasi-Polish spaces, Section 10,
recalling Kechris 8.19. No novelty or priority claimed.
-/
/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
Material Lean proof authorship: OpenAI Codex.
Classical strong Choquet criterion: consulted Brian Lemma 3.5 and Dorais–Mummert.
Countable response-cover subtree inspiration: Ruiyuan Chen, Theorem 11.7.
The ambient Gδ node-implication finish is proved here. The closed-trap completeness
argument adapts Apache-2.0 Choquet source51def6feb5e4469cce2396dfa4c9fa4f3b933d82.
-/
module
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Metrizable.Urysohn
public section
open Set Filter Topology TopologicalSpace
open scoped Topology
namespace StrongChoquet

/-- The marked point must remain inside the second player's response. -/
structure Move (X : Type u) [TopologicalSpace X] where
  point : X
  region : Set X
  isOpen : IsOpen region
  mem : point ∈ region

/-- The current marked move and the full reverse opponent history are available. -/
structure Strategy (X : Type u) [TopologicalSpace X] where
  move : Move X → List (Move X) → Set X
  isOpen : ∀ a h, IsOpen (move a h)
  contains : ∀ a h, a.point ∈ move a h
  subset : ∀ a h, move a h ⊆ a.region

@[expose] def history {X : Type u} [TopologicalSpace X] (a : ℕ → Move X) :
    ℕ → List (Move X)
  | 0 => []
  | n + 1 => a n :: history a n

@[expose] def Follows {X : Type u} [TopologicalSpace X] (σ : Strategy X)
    (a : ℕ → Move X) : Prop :=
  ∀ n, (a (n+1)).region ⊆ σ.move (a n) (history a n)

@[expose] def Winning {X : Type u} [TopologicalSpace X] (σ : Strategy X) : Prop :=
  ∀ a, Follows σ a → (⋂ n, σ.move (a n) (history a n)).Nonempty

@[expose] def Strong (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ σ : Strategy X, Winning σ

@[simp] theorem history_length {X : Type u} [TopologicalSpace X]
    (a : ℕ → Move X) (n : ℕ) : (history a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

/-- A legal play has the same intersection for the first moves and second replies. -/
theorem intersection_eq {X : Type u} [TopologicalSpace X]
    (σ : Strategy X) (a : ℕ → Move X) (ha : Follows σ a) :
    (⋂ n, (a n).region) = ⋂ n, σ.move (a n) (history a n) := by
  ext x
  simp only [mem_iInter]
  exact ⟨fun h n => ha n (h (n+1)), fun h n => σ.subset _ _ (h n)⟩

private def playState {X : Type u} [TopologicalSpace X] (σ : Strategy X) (a₀ : Move X) :
    ℕ → Move X × List (Move X)
  | 0 => (a₀, [])
  | n+1 =>
    let q := playState σ a₀ n
    (⟨q.1.point, σ.move q.1 q.2, σ.isOpen _ _, σ.contains _ _⟩, q.1 :: q.2)

/-- Every legal initial marked move admits an actual compatible infinite play. -/
theorem exists_legalPlay {X : Type u} [TopologicalSpace X]
    (σ : Strategy X) (a₀ : Move X) :
    ∃ a : ℕ → Move X, a 0 = a₀ ∧ Follows σ a := by
  let a n := (playState σ a₀ n).1
  have hh (n : ℕ) : (playState σ a₀ n).2 = history a n := by
    induction n with
    | zero => rfl
    | succ n ih => change a n :: (playState σ a₀ n).2 = _; rw [ih]; rfl
  refine ⟨a, rfl, fun n => ?_⟩
  change σ.move (a n) (playState σ a₀ n).2 ⊆ σ.move (a n) (history a n)
  rw [hh]

/-- On an empty space no first marked move exists; the winning universal
quantification is explicitly vacuous. -/
theorem strong_of_isEmpty {X : Type u} [TopologicalSpace X] [IsEmpty X] : Strong X := by
  let σ : Strategy X :=
    { move a _ := isEmptyElim a.point
      isOpen a _ := isEmptyElim a.point
      contains a _ := isEmptyElim a.point
      subset a _ := isEmptyElim a.point }
  exact ⟨σ, fun a _ => isEmptyElim (a 0).point⟩

section MetricStrategy
open Metric
variable {X : Type u} [MetricSpace X]

private theorem exists_radius (n : ℕ) (a : Move X) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (1/2 : ℝ)^n ∧ closedBall a.point r ⊆ a.region := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (a.isOpen.mem_nhds a.mem)
  exact ⟨min r ((1/2 : ℝ)^n), lt_min hr (pow_pos (by norm_num) _),
    min_le_right _ _, (closedBall_subset_closedBall (min_le_left _ _)).trans hball⟩

private noncomputable def radius (n : ℕ) (a : Move X) : ℝ :=
  (exists_radius n a).choose

private theorem radius_spec (n : ℕ) (a : Move X) :
    0 < radius n a ∧ radius n a ≤ (1/2 : ℝ)^n ∧
      closedBall a.point (radius n a) ⊆ a.region :=
  (exists_radius n a).choose_spec

private noncomputable def metricStrategy : Strategy X where
  move a h := ball a.point (radius h.length a)
  isOpen _ _ := isOpen_ball
  contains a h := mem_ball_self (radius_spec h.length a).1
  subset a h := ball_subset_closedBall.trans (radius_spec h.length a).2.2

/-- A complete metric gives an actual full-history strong Choquet strategy.
The marked point is preserved, and shrinking closed balls are never assumed compact. -/
theorem strong_of_completeMetric [CompleteSpace X] : Strong X := by
  refine ⟨metricStrategy, fun a ha => ?_⟩
  let c : ℕ → X := fun n => (a n).point
  let r : ℕ → ℝ := fun n => radius n (a n)
  have hp (n : ℕ) : 0 < r n := (radius_spec n (a n)).1
  have hb (n : ℕ) : r n ≤ (1/2 : ℝ)^n := (radius_spec n (a n)).2.1
  have ht (n : ℕ) : closedBall (c (n+1)) (r (n+1)) ⊆ ball (c n) (r n) := by
    simpa only [metricStrategy, history_length, c, r] using
      ((radius_spec (n+1) (a (n+1))).2.2.trans (ha n))
  have hall {n m : ℕ} (hnm : n ≤ m) : closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact ((ht m).trans ball_subset_closedBall).trans ih
  have hf (N : ℕ) : (⋂ n ≤ N, closedBall (c n) (r n)).Nonempty := by
    exact ⟨c N, mem_iInter.mpr fun n => mem_iInter.mpr fun hn =>
      hall hn (mem_closedBall_self (hp N).le)⟩
  have hz : Tendsto (fun n : ℕ => 2 * (1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul (2 : ℝ)
  have hd : Tendsto (fun n => diam (closedBall (c n) (r n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => diam_nonneg) (fun n => ?_) hz
    exact (diam_closedBall (hp n).le).trans
      (mul_le_mul_of_nonneg_left (hb n) (by norm_num))
  obtain ⟨x, hx⟩ := Metric.nonempty_iInter_of_nonempty_biInter
    (fun _ => isClosed_closedBall) (fun _ => isBounded_closedBall) hf hd
  exact ⟨x, mem_iInter.mpr fun n => by
    simpa only [metricStrategy, history_length, c, r] using ht n (mem_iInter.mp hx (n+1))⟩
end MetricStrategy

theorem strong_of_completelyMetrizable {X : Type u} [TopologicalSpace X]
    [IsCompletelyMetrizableSpace X] : Strong X := by
  let := upgradeIsCompletelyMetrizable X
  exact strong_of_completeMetric

/-- A countable intersection of open subsets of a complete metric space has a
compatible complete metric. The proof uses a closed diagonal in the countable
product of Mathlib's boundary-blown-up complete copies of the open subsets. -/
theorem completelyMetrizable_iInter {Y : Type u} [MetricSpace Y] [CompleteSpace Y]
    (U : ℕ → Opens Y) : IsCompletelyMetrizableSpace (⋂ n, (U n : Set Y)) := by
  let Z := ∀ n, Opens.CompleteCopy (U n)
  let D : Set Z := {z | ∀ n, (z n).val = (z 0).val}
  have hD : IsClosed D := by
    have h : D = ⋂ n, {z : Z | (z n).val = (z 0).val} := by
      ext z; simp [D]
    rw [h]
    exact isClosed_iInter fun n => isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0))
  let e : (⋂ n, (U n : Set Y)) ≃ D :=
    { toFun := fun x => ⟨fun n => ⟨x.val, mem_iInter.mp x.property n⟩, fun _ => rfl⟩
      invFun := fun z => ⟨(z.val 0).val, mem_iInter.mpr fun n => by
        rw [← z.property n]; exact (z.val n).property⟩
      left_inv := fun _ => rfl
      right_inv := fun z => by
        apply Subtype.ext
        funext n
        apply Subtype.ext
        exact (z.property n).symm }
  let h : (⋂ n, (U n : Set Y)) ≃ₜ D :=
    { e with
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_pi fun n => continuous_subtype_val.subtype_mk _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          ((continuous_apply 0).comp continuous_subtype_val) }
  have : IsCompletelyMetrizableSpace D := hD.isCompletelyMetrizableSpace
  exact h.isClosedEmbedding.IsCompletelyMetrizableSpace

theorem completelyMetrizable_of_isGdelta {Y : Type u} [MetricSpace Y] [CompleteSpace Y]
    {s : Set Y} (hs : IsGδ s) : IsCompletelyMetrizableSpace s := by
  obtain ⟨U, hU, rfl⟩ := hs.eq_iInter_nat
  exact completelyMetrizable_iInter (fun n => ⟨U n, hU n⟩)

section Converse
open Metric
variable {X : Type v} [TopologicalSpace X] {Y : Type u} [MetricSpace Y]
  (f : X → Y) (σ : Strategy X)

/-- Internal tree state: the ambient open region has exactly the trace of the
last actual strategy response. The empty history denotes the initial universe. -/
private structure Node where
  past : List (Move X)
  region : Set Y
  isOpen : IsOpen region
  trace : ∀ x : X, f x ∈ region ↔
    match past with
    | [] => True
    | a :: h => x ∈ σ.move a h
  hit : ∃ x : X, f x ∈ region

private theorem exists_child (hf : IsEmbedding f) (q : Node f σ) (x : X) (hx : f x ∈ q.region) :
    ∃ q' : Node f σ, ∃ a : Move X,
      q'.past = a :: q.past ∧ (∀ z ∈ a.region, f z ∈ q.region) ∧ q'.region ⊆ q.region ∧
      (∀ y ∈ q'.region, ∀ z ∈ q'.region,
        dist y z ≤ (1/2 : ℝ)^q.past.length) ∧ f x ∈ q'.region := by
  let ε : ℝ := (1/2 : ℝ)^q.past.length / 2
  have hε : 0 < ε := half_pos (pow_pos (by norm_num) _)
  let a : Move X := ⟨x, f ⁻¹' (q.region ∩ ball (f x) ε),
    (q.isOpen.inter isOpen_ball).preimage hf.continuous,
    ⟨hx, mem_ball_self hε⟩⟩
  obtain ⟨W, hWo, hW⟩ := hf.isInducing.isOpen_iff.mp (σ.isOpen a q.past)
  have hWz (z : X) : f z ∈ W ↔ z ∈ σ.move a q.past := by
    change z ∈ f ⁻¹' W ↔ _
    rw [hW]
  let V : Set Y := (W ∩ q.region) ∩ ball (f x) ε
  have htrace (z : X) : f z ∈ V ↔ z ∈ σ.move a q.past := by
    constructor
    · intro hz; exact (hWz z).mp hz.1.1
    · intro hz
      have ha := σ.subset a q.past hz
      exact ⟨⟨(hWz z).mpr hz, ha.1⟩, ha.2⟩
  have hxV : f x ∈ V := (htrace x).mpr (σ.contains a q.past)
  let q' : Node f σ := ⟨a :: q.past, V, (hWo.inter q.isOpen).inter isOpen_ball,
    htrace, ⟨x, hxV⟩⟩
  refine ⟨q', a, rfl, fun _ hz => hz.1, fun _ hy => hy.1.2, ?_, hxV⟩
  intro y hy z hz
  have hy' : dist y (f x) < ε := hy.2
  have hz' : dist (f x) z < ε := by simpa [dist_comm] using hz.2
  have hd := (dist_triangle y (f x) z).trans_lt (add_lt_add hy' hz')
  dsimp [ε] at hd
  linarith

private theorem exists_children [SecondCountableTopology Y] (hf : IsEmbedding f) (q : Node f σ) :
    ∃ g : ℕ → Node f σ,
      (∀ n, ∃ a : Move X, (g n).past = a :: q.past ∧
        (∀ z ∈ a.region, f z ∈ q.region) ∧ (g n).region ⊆ q.region ∧
        ∀ y ∈ (g n).region, ∀ z ∈ (g n).region,
          dist y z ≤ (1/2 : ℝ)^q.past.length) ∧
      ∀ x : X, f x ∈ q.region → ∃ n, f x ∈ (g n).region := by
  classical
  let I := {x : X // f x ∈ q.region}
  have : Nonempty I := by
    obtain ⟨x, hx⟩ := q.hit
    exact ⟨⟨x, hx⟩⟩
  choose c a hp hi hs hd hx using fun i : I => exists_child f σ hf q i.val i.property
  obtain ⟨e, he⟩ := (HereditarilyLindelofSpace.isLindelof (⋃ i, (c i).region)).indexed_countable_subcover
    (fun i => (c i).region) (fun i => (c i).isOpen) subset_rfl
  refine ⟨fun n => c (e n), fun n => ⟨a (e n), hp (e n), hi (e n), hs (e n), hd (e n)⟩, ?_⟩
  intro x hxq
  exact mem_iUnion.mp (he (mem_iUnion.mpr ⟨⟨x, hxq⟩, hx ⟨x, hxq⟩⟩))

/-- In a second-countable metric ambient space, a strongly Choquet embedded
subspace is Gδ. All node implications are imposed, so the branch is coherent. -/
theorem isGdelta_range_of_strong [SecondCountableTopology Y] (hf : IsEmbedding f)
    (hstrong : Strong X) : IsGδ (range f) := by
  classical
  obtain ⟨σ, hσ⟩ := hstrong
  by_cases hX : Nonempty X
  · let r : Node f σ := ⟨[], univ, isOpen_univ,
      fun _ => iff_of_true (mem_univ _) True.intro, ⟨Classical.choice hX, mem_univ _⟩⟩
    let c (q : Node f σ) : ℕ → Node f σ := (exists_children f σ hf q).choose
    have hc (q : Node f σ) := (exists_children f σ hf q).choose_spec
    let t : List ℕ → Node f σ := fun l => l.foldr (fun n q => c q n) r
    let G : Set Y := ⋂ l : List ℕ, (t l).regionᶜ ∪ ⋃ n, (t (n :: l)).region
    have hG : IsGδ G := IsGδ.iInter fun l =>
      (t l).isOpen.isClosed_compl.isGδ.union
        (isOpen_iUnion fun n => (t (n :: l)).isOpen).isGδ
    have hRG : range f ⊆ G := by
      rintro _ ⟨x, rfl⟩
      apply mem_iInter.mpr
      intro l
      by_cases hx : f x ∈ (t l).region
      · right
        obtain ⟨n, hn⟩ := (hc (t l)).2 x hx
        exact mem_iUnion.mpr ⟨n, hn⟩
      · exact Or.inl hx
    have hGR : G ⊆ range f := by
      intro y hy
      have advance (l : List ℕ) (h : y ∈ (t l).region) :
          ∃ n, y ∈ (t (n :: l)).region := by
        rcases mem_iInter.mp hy l with hn | hn
        · exact (hn h).elim
        · exact mem_iUnion.mp hn
      let step (p : {l : List ℕ // y ∈ (t l).region}) :
          {l : List ℕ // y ∈ (t l).region} :=
        ⟨(advance p.val p.property).choose :: p.val,
          (advance p.val p.property).choose_spec⟩
      let p : ℕ → {l : List ℕ // y ∈ (t l).region} :=
        Nat.rec ⟨[], mem_univ _⟩ (fun _ q => step q)
      let q (n : ℕ) := t (p n).val
      have hstep (n : ℕ) : ∃ a : Move X,
          (q (n+1)).past = a :: (q n).past ∧
          (∀ z ∈ a.region, f z ∈ (q n).region) ∧
          (q (n+1)).region ⊆ (q n).region ∧
          ∀ z ∈ (q (n+1)).region, ∀ w ∈ (q (n+1)).region,
            dist z w ≤ (1/2 : ℝ)^(q n).past.length := by
        exact (hc (q n)).1 (advance (p n).val (p n).property).choose
      choose a hap hai _ hdiam using hstep
      have hh (n : ℕ) : (q n).past = history a n := by
        induction n with
        | zero => rfl
        | succ n ih => rw [hap n, ih]; rfl
      have hfollow : Follows σ a := by
        intro n x hx
        have hxr := hai (n+1) x hx
        have ht := (q (n+1)).trace x
        rw [hap n] at ht
        simpa only [hh n] using ht.mp hxr
      obtain ⟨x, hx⟩ := hσ a hfollow
      have hxr (n : ℕ) : f x ∈ (q (n+1)).region := by
        have ht := (q (n+1)).trace x
        rw [hap n] at ht
        exact ht.mpr (by simpa only [hh n] using mem_iInter.mp hx n)
      have hd (n : ℕ) : dist (f x) y ≤ (1/2 : ℝ)^n := by
        simpa only [hh n, history_length] using
          hdiam n (f x) (hxr n) y (p (n+1)).property
      have hz : Tendsto (fun _ : ℕ => dist (f x) y) atTop (𝓝 0) :=
        squeeze_zero (fun _ => dist_nonneg) hd
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      exact ⟨x, dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)⟩
    exact (hRG.antisymm hGR) ▸ hG
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simpa only [range_eq_empty] using (IsGδ.empty : IsGδ (∅ : Set Y))
end Converse

/-- The converse: the winning strong game strategy supplies a compatible
complete metric, using the Gδ image in the completion of an arbitrary compatible metric. -/
theorem completelyMetrizable_of_strong {X : Type u} [TopologicalSpace X]
    [MetrizableSpace X] [SecondCountableTopology X] (h : Strong X) :
    IsCompletelyMetrizableSpace X := by
  let := metrizableSpaceMetric X
  let f : X → UniformSpace.Completion X := fun x => x
  have hf : IsEmbedding f := (UniformSpace.Completion.isUniformEmbedding_coe X).isEmbedding
  have hg : IsGδ (range f) := isGdelta_range_of_strong f hf h
  have : IsCompletelyMetrizableSpace (range f) := completelyMetrizable_of_isGdelta hg
  exact hf.toHomeomorph.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- Classical strong Choquet characterization, explicitly in the
second-countable metrizable scope, including the full converse. -/
theorem strong_iff_completelyMetrizable {X : Type u} [TopologicalSpace X]
    [MetrizableSpace X] [SecondCountableTopology X] :
    Strong X ↔ IsCompletelyMetrizableSpace X := by
  constructor
  · exact completelyMetrizable_of_strong
  · intro h
    have := h
    exact strong_of_completelyMetrizable

theorem polish_iff_strong {X : Type u} [TopologicalSpace X]
    [MetrizableSpace X] [SecondCountableTopology X] : PolishSpace X ↔ Strong X := by
  constructor
  · intro h
    have := h
    exact strong_of_completelyMetrizable
  · intro h
    have := completelyMetrizable_of_strong h
    infer_instance

end StrongChoquet

open Set Topology TopologicalSpace
namespace OpenPolish
open StrongChoquet

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : X → Y) (hc : Continuous f) (ho : IsOpenMap f)
  (hs : Function.Surjective f) (σ : Strategy X)

private def trap : List (Move X) → Set X
  | [] => univ
  | b :: h => σ.move b h

private theorem trap_open (h : List (Move X)) : IsOpen (trap σ h) := by
  cases h with
  | nil => exact isOpen_univ
  | cons b h => exact σ.isOpen b h

private noncomputable def liftRegion (a : Move Y) (h : List (Move X)) : Set X := by
  classical
  exact f ⁻¹' a.region ∩ if a.point ∈ f '' trap σ h then trap σ h else univ

include hc in
private theorem liftRegion_open (a : Move Y) (h : List (Move X)) :
    IsOpen (liftRegion f σ a h) := by
  unfold liftRegion
  apply (a.isOpen.preimage hc).inter
  split_ifs
  · exact trap_open σ h
  · exact isOpen_univ

include hs in
private theorem exists_lift (a : Move Y) (h : List (Move X)) :
    ∃ x, x ∈ liftRegion f σ a h ∧ f x = a.point := by
  classical
  by_cases ha : a.point ∈ f '' trap σ h
  · have havail := ha
    obtain ⟨x, hx, he⟩ := ha
    exact ⟨x, by simp only [liftRegion, ite_eq_left havail, mem_inter_iff, mem_preimage];
                  exact ⟨he ▸ a.mem, hx⟩, he⟩
  · obtain ⟨x, he⟩ := hs a.point
    exact ⟨x, by simp only [liftRegion, ite_eq_right ha, inter_univ, mem_preimage];
                  exact he ▸ a.mem, he⟩

private noncomputable def liftMove (a : Move Y) (h : List (Move X)) : Move X where
  point := (exists_lift f hs σ a h).choose
  region := liftRegion f σ a h
  isOpen := liftRegion_open f hc σ a h
  mem := (exists_lift f hs σ a h).choose_spec.1

private theorem liftMove_point (a : Move Y) (h : List (Move X)) :
    f (liftMove f hc hs σ a h).point = a.point :=
  (exists_lift f hs σ a h).choose_spec.2

private theorem liftMove_preimage (a : Move Y) (h : List (Move X)) :
    (liftMove f hc hs σ a h).region ⊆ f ⁻¹' a.region :=
  inter_subset_left

private theorem liftMove_trap (a : Move Y) (h : List (Move X))
    (ha : a.point ∈ f '' trap σ h) :
    (liftMove f hc hs σ a h).region ⊆ trap σ h := by
  classical
  change f ⁻¹' a.region ∩ (if _ then _ else _) ⊆ _
  rw [ite_eq_left ha]
  exact inter_subset_right

/-- Reconstruct the source history from oldest to newest. When a marked point cannot be lifted into the preceding source response, the
lift falls back to the full preimage, making the strategy total on arbitrary histories. -/
private noncomputable def liftHistory : List (Move Y) → List (Move X)
  | [] => []
  | b :: h => liftMove f hc hs σ b (liftHistory h) :: liftHistory h

/-- The image of the source response, with coherent lifts of all earlier moves.
The image is open and retains the actual marked target point. -/
noncomputable def imageStrategy : Strategy Y where
  move a h := f '' σ.move (liftMove f hc hs σ a (liftHistory f hc hs σ h))
    (liftHistory f hc hs σ h)
  isOpen _ _ := ho _ (σ.isOpen _ _)
  contains a h := ⟨_, σ.contains _ _, liftMove_point f hc hs σ a _⟩
  subset a h := by
    rintro y ⟨x, hx, rfl⟩
    exact liftMove_preimage f hc hs σ a _ (σ.subset _ _ hx)

/-- A legal target play lifts to a single coherent legal source play.
We map an actual common source point; images are not commuted with intersections. -/
theorem imageStrategy_winning (hw : Winning σ) :
    Winning (imageStrategy f hc ho hs σ) := by
  classical
  intro a ha
  let b (n : ℕ) := liftMove f hc hs σ (a n) (liftHistory f hc hs σ (history a n))
  have hh (n : ℕ) : liftHistory f hc hs σ (history a n) = history b n := by
    induction n with
    | zero => rfl
    | succ n ih => change b n :: liftHistory f hc hs σ (history a n) = _
                   rw [ih]; rfl
  have hr (n : ℕ) :
      (imageStrategy f hc ho hs σ).move (a n) (history a n) =
        f '' σ.move (b n) (history b n) := by
    change f '' σ.move (b n) (liftHistory f hc hs σ (history a n)) = _
    rw [hh]
  have hb : Follows σ b := by
    intro n
    have hm : (a (n+1)).point ∈ f '' trap σ (liftHistory f hc hs σ (history a (n+1))) := by
      change (a (n+1)).point ∈ f '' σ.move (b n)
        (liftHistory f hc hs σ (history a n))
      rw [hh, ← hr]
      exact ha n (a (n+1)).mem
    have ht := liftMove_trap f hc hs σ (a (n+1)) _ hm
    change (b (n+1)).region ⊆ σ.move (b n)
      (liftHistory f hc hs σ (history a n)) at ht
    rwa [hh] at ht
  obtain ⟨x, hx⟩ := hw b hb
  refine ⟨f x, mem_iInter.mpr fun n => ?_⟩
  rw [hr]
  exact ⟨x, mem_iInter.mp hx n, rfl⟩

include f hc ho hs

/-- Continuous open surjections preserve the strong Choquet property, without
separation, countability or metrizability assumptions on either space. -/
theorem strong_image (hX : Strong X) : Strong Y := by
  obtain ⟨σ, hw⟩ := hX
  exact ⟨imageStrategy f hc ho hs σ, imageStrategy_winning f hc ho hs σ hw⟩

/-- Second countability descends from the source; no separate countability
hypothesis on the metrizable target is required. -/
theorem completelyMetrizable_image [SecondCountableTopology X]
    [IsCompletelyMetrizableSpace X] [MetrizableSpace Y] :
    IsCompletelyMetrizableSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  exact completelyMetrizable_of_strong
    (strong_image f hc ho hs strong_of_completelyMetrizable)

/-- A continuous open metrizable image of a Polish space is Polish. This gives
a compatible complete metric, not completeness of an arbitrary supplied metric. -/
theorem polish_image [PolishSpace X] [MetrizableSpace Y] : PolishSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  let : IsCompletelyMetrizableSpace Y := completelyMetrizable_image f hc ho hs
  infer_instance

/-- A regular Hausdorff open continuous image is metrizable by inherited second
countability and Urysohn, hence Polish. Mere Hausdorffness is not substituted. -/
theorem polish_image_of_t3 [PolishSpace X] [T3Space Y] : PolishSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  exact polish_image f hc ho hs

end OpenPolish
