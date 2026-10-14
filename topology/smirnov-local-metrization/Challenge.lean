/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
  Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Developed with AI assistance (OpenAI Codex); no human review is claimed.
-/
module

public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.PerfectlyNormal
public import Mathlib.Topology.Compactness.Paracompact

/-! The Nagata–Smirnov development below is reused verbatim from registered
PALOMAR-2026-10-14-000001, source commit 6aa68b2cb67719a187e64de29567443575eb560e.
It is included to make this Challenge canonical-import-only; the new contribution
is the subsequent point-finite-cover construction and Smirnov criterion. -/

@[expose] public section

/-!
# Sigma locally finite bases and open exhaustion

The layers of a sigma locally finite basis can have arbitrary cardinality.
Regularity supplies a countable open cover with closures contained in
each prescribed open set. This proves perfect normality without any
second-countability or separability assumption.

Reference: K. Sakai, *Geometric Aspects of General Topology*, second-edition
author manuscript (November 2, 2023), chapter 2, Lemma 2.3.3.
-/

open Set TopologicalSpace Topology

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- An open basis expressed as countably many locally finite families.
No individual family is required to be countable. -/
def HasSigmaLocallyFiniteBasis (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ B : ℕ → Set (Set X),
    (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
      IsTopologicalBasis (⋃ n, B n)

/-- The union of all members of one basis layer whose closures lie in `U`. -/
def basisShrinkLayer (B : ℕ → Set (Set X)) (U : Set X) (n : ℕ) : Set X :=
  ⋃ V : {V : B n // closure (V : Set X) ⊆ U}, (V.1 : Set X)

theorem basisShrinkLayer_isOpen {B : ℕ → Set (Set X)}
    (hB : IsTopologicalBasis (⋃ n, B n)) (U : Set X) (n : ℕ) :
    IsOpen (basisShrinkLayer B U n) := by
  exact isOpen_iUnion fun V => hB.isOpen (mem_iUnion_of_mem n V.1.2)

theorem closure_basisShrinkLayer_subset {B : ℕ → Set (Set X)}
    (hB : ∀ n, LocallyFinite (fun V : B n => (V : Set X))) (U : Set X) (n : ℕ) :
    closure (basisShrinkLayer B U n) ⊆ U := by
  have hfin : LocallyFinite
      (fun V : {V : B n // closure (V : Set X) ⊆ U} => (V.1 : Set X)) :=
    (hB n).comp_injective Subtype.val_injective
  rw [basisShrinkLayer, hfin.closure_iUnion]
  exact iUnion_subset fun V => V.2

theorem iUnion_basisShrinkLayer_eq [RegularSpace X] {B : ℕ → Set (Set X)}
    (hB : IsTopologicalBasis (⋃ n, B n)) {U : Set X} (hU : IsOpen U) :
    (⋃ n, basisShrinkLayer B U n) = U := by
  apply Subset.antisymm
  · refine iUnion_subset fun n => iUnion_subset fun V => ?_
    exact subset_closure.trans V.2
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_closure_subset (hU.mem_nhds hx)
    obtain ⟨n, hVn⟩ := mem_iUnion.mp hV
    exact mem_iUnion_of_mem n (mem_iUnion_of_mem ⟨⟨V, hVn⟩, hVU⟩ hxV)

/-- Every open set admits a countable open cover whose closures stay inside it.
The cover is not asserted to be increasing. -/
theorem HasSigmaLocallyFiniteBasis.exists_open_exhaustion [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) {U : Set X} (hU : IsOpen U) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧
      (∀ n, closure (V n) ⊆ U) ∧ (⋃ n, V n) = U := by
  obtain ⟨B, hfin, hB⟩ := h
  exact ⟨basisShrinkLayer B U, basisShrinkLayer_isOpen hB U,
    closure_basisShrinkLayer_subset hfin U, iUnion_basisShrinkLayer_eq hB hU⟩

theorem HasSigmaLocallyFiniteBasis.hasSeparatingCover [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) {s t : Set X}
    (ht : IsClosed t) (hst : Disjoint s t) : HasSeparatingCover s t := by
  obtain ⟨V, hVo, hVsub, hVcov⟩ := h.exists_open_exhaustion ht.isOpen_compl
  refine ⟨V, ?_, fun n => ⟨hVo n, ?_⟩⟩
  · rw [hVcov]
    exact hst.subset_compl_right
  · exact disjoint_compl_left.mono_left (hVsub n)

/-- A regular space with a sigma locally finite basis is normal. -/
theorem HasSigmaLocallyFiniteBasis.normalSpace [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) : NormalSpace X where
  normal _s _t hs ht hst := hasSeparatingCovers_iff_separatedNhds.mp
    ⟨h.hasSeparatingCover ht hst, h.hasSeparatingCover hs hst.symm⟩

/-- A regular space with a sigma locally finite basis is perfectly normal. -/
theorem HasSigmaLocallyFiniteBasis.perfectlyNormalSpace [RegularSpace X]
    (h : HasSigmaLocallyFiniteBasis X) : PerfectlyNormalSpace X where
  toNormalSpace := h.normalSpace
  closed_gdelta s hs := by
    obtain ⟨V, -, hVsub, hVcov⟩ := h.exists_open_exhaustion hs.isOpen_compl
    have hcl : (⋃ n, closure (V n)) = sᶜ := by
      apply Subset.antisymm
      · exact iUnion_subset hVsub
      · rw [← hVcov]
        exact iUnion_mono fun n => subset_closure
    have heq : s = ⋂ n, (closure (V n))ᶜ := by
      rw [← compl_iUnion, hcl, compl_compl]
    rw [heq]
    exact IsGδ.iInter_of_isOpen fun n => isClosed_closure.isOpen_compl

end NagataSmirnov

/-!
# Compatible metric infrastructure for locally finite coordinate families

An arbitrary locally finite family of bounded continuous coordinates gives a
continuous map into a metric space of bounded functions with the uniform metric.
Only the layers, rather than their coordinate index types, will be countable.
-/

open Set Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace NagataSmirnov

variable {X I : Type*} [TopologicalSpace X]

/-- Locally finite supports upgrade coordinatewise continuity to continuity
for the uniform metric on bounded functions. The index type is arbitrary. -/
theorem continuous_boundedCoordinates [TopologicalSpace I] [DiscreteTopology I]
    (f : I → C(X, ℝ)) (hf : ∀ i x, f i x ∈ Icc (0 : ℝ) 1)
    (hl : LocallyFinite (fun i => Function.support (f i))) :
    Continuous (fun x => BoundedContinuousFunction.mkOfDiscrete
      (fun i => f i x) 1
      (fun i j => Real.dist_le_of_mem_Icc_01 (hf i x) (hf j x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, hU, hfin⟩ := hl x
  have hc : ∀ᶠ y in 𝓝 x,
      ∀ i ∈ {i | (Function.support (f i) ∩ U).Nonempty},
        dist (f i y) (f i x) < ε / 2 := by
    apply (eventually_all_finite hfin).mpr
    intro i hi
    exact (f i).continuous.continuousAt.eventually
      (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hU, hc] with y hy hcy
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.dist_le (half_pos hε).le).mpr
  intro i
  by_cases hi : i ∈ {i | (Function.support (f i) ∩ U).Nonempty}
  · exact (hcy i hi).le
  · have hy0 : f i y = 0 := by
      by_contra h
      exact hi ⟨y, h, hy⟩
    have hx0 : f i x = 0 := by
      by_contra h
      exact hi ⟨x, h, mem_of_mem_nhds hU⟩
    simpa [hy0, hx0] using (half_pos hε).le

end NagataSmirnov

/-!
# Locally finite metric basis layers

Each metric ball cover at radius `1 / (n + 1)` has a locally finite open refinement.
The ranges of those refinements form an open basis. The index set of each layer
can have arbitrary cardinality: only the sequence of layers is countable.
-/

open Set TopologicalSpace Metric

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- Every metrizable space admits an open basis that is a countable union of locally
finite families. No separability or countability of the individual layers is required. -/
theorem exists_sigmaLocallyFiniteBasis [MetrizableSpace X] :
    ∃ B : ℕ → Set (Set X),
      (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
        IsTopologicalBasis (⋃ n, B n) := by
  classical
  let : MetricSpace X := metrizableSpaceMetric X
  have hr : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ) := fun n =>
    div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hc : ∀ n : ℕ, ⋃ x : X, ball x (1 / (n + 1 : ℝ)) = univ := by
    intro n
    exact iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_ball_self (hr n)⟩
  choose V hVo hVc hVf hVs using fun n : ℕ =>
    precise_refinement (fun x : X => ball x (1 / (n + 1 : ℝ)))
      (fun _ => isOpen_ball) (hc n)
  refine ⟨fun n => range (V n), fun n => (hVf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    rcases mem_iUnion.mp hU with ⟨n, x, rfl⟩
    exact hVo n x
  · intro x U hx hU
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨c, hxc⟩ := iUnion_eq_univ_iff.mp (hVc n) x
    refine ⟨V n c, mem_iUnion.mpr ⟨n, mem_range_self c⟩, hxc, ?_⟩
    intro y hy
    apply hεU
    have hyc := hVs n c hy
    have hxc' := hVs n c hxc
    rw [mem_ball] at hyc hxc' ⊢
    calc
      dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      _ = dist y c + dist x c := by rw [dist_comm c x]
      _ < 1 / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := add_lt_add hyc hxc'
      _ < ε := (add_lt_add hn hn).trans_eq (add_halves ε)

end NagataSmirnov

/-!
# Nagata–Smirnov metrization

The sigma locally finite basis is allowed arbitrary cardinality in every layer.
Perfect normality supplies cozero coordinates; local finiteness makes each
layer continuous for the uniform metric. A countable product of these metric
function spaces induces the given topology.

Reference: Katsuro Sakai, Geometric Aspects of General Topology, second-edition
manuscript (2023), Theorem 2.3.4(a),(c) and Lemma 2.3.3.
-/

open Set Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- A sigma locally finite cozero basis induces a topology from a countable
product of metric function spaces. Individual layers can be uncountable. -/
theorem pseudoMetrizable_of_cozero_basis
    (B : ℕ → Set (Set X))
    (hl : ∀ n, LocallyFinite (fun U : B n => (U : Set X)))
    (hb : IsTopologicalBasis (⋃ n, B n))
    (f : ∀ n, B n → C(X, ℝ))
    (hf : ∀ n U x, f n U x ∈ Icc (0 : ℝ) 1)
    (hzero : ∀ n U x, f n U x = 0 ↔ x ∉ (U : Set X)) :
    PseudoMetrizableSpace X := by
  classical
  let : ∀ n, TopologicalSpace (B n) := fun _ => ⊥
  have : ∀ n, DiscreteTopology (B n) := fun _ => ⟨rfl⟩
  have : PseudoMetrizableSpace (∀ n, B n →ᵇ ℝ) := inferInstance
  let F : X → ∀ n, B n →ᵇ ℝ := fun x n =>
    BoundedContinuousFunction.mkOfDiscrete (fun U => f n U x) 1
      (fun U V => Real.dist_le_of_mem_Icc_01 (hf n U x) (hf n V x))
  have hF : Continuous F := by
    apply continuous_pi
    intro n
    apply continuous_boundedCoordinates (f n) (hf n)
    apply (hl n).subset
    intro U x hx
    exact not_not.mp (fun h => hx ((hzero n U x).mpr h))
  have hi : IsInducing F := by
    apply isInducing_iff_nhds.mpr
    intro x
    refine le_antisymm (hF.continuousAt.le_comap) ?_
    apply hb.nhds_hasBasis.ge_iff.mpr
    rintro U ⟨hUB, hxU⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hUB
    let V : B n := ⟨U, hn⟩
    have hpos : 0 < f n V x := lt_of_le_of_ne (hf n V x).1
      (Ne.symm (fun h => ((hzero n V x).mp h) hxU))
    have hc : Continuous (fun z : (∀ n, B n →ᵇ ℝ) => z n V) :=
      (BoundedContinuousFunction.lipschitz_eval_const V).continuous.comp (continuous_apply n)
    have hn : {z : (∀ n, B n →ᵇ ℝ) | 0 < z n V} ∈ 𝓝 (F x) :=
      (isOpen_Ioi.preimage hc).mem_nhds hpos
    apply mem_of_superset (preimage_mem_comap hn)
    intro y hy
    have : f n V y ≠ 0 := ne_of_gt hy
    exact not_not.mp (fun h => this ((hzero n V y).mpr h))
  exact hi.pseudoMetrizableSpace

/-- The sufficiency direction of the full Nagata–Smirnov theorem. -/
theorem HasSigmaLocallyFiniteBasis.metrizableSpace [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) : MetrizableSpace X := by
  classical
  let : PerfectlyNormalSpace X := h.perfectlyNormalSpace
  obtain ⟨B, hl, hb⟩ := h
  have hex : ∀ n (U : B n), ∃ f : C(X, ℝ),
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, f x = 0 ↔ x ∉ (U : Set X)) := by
    intro n U
    obtain ⟨f, hf, hfr⟩ :=
      perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.mp
        (inferInstance : PerfectlyNormalSpace X) (U : Set X)ᶜ
        (hb.isOpen (mem_iUnion.mpr ⟨n, U.property⟩)).isClosed_compl
    refine ⟨f, hfr, ?_⟩
    intro x
    exact Iff.symm (show x ∈ (U : Set X)ᶜ ↔ f x = 0 by rw [hf]; rfl)
  choose f hf hz using hex
  let : PseudoMetrizableSpace X := pseudoMetrizable_of_cozero_basis B hl hb f hf hz
  infer_instance

/-- Full Nagata–Smirnov: a regular Hausdorff space is metrizable exactly when
it has an open basis which is a countable union of locally finite families. -/
theorem nagata_smirnov [T3Space X] :
    MetrizableSpace X ↔ HasSigmaLocallyFiniteBasis X := by
  constructor
  · intro h
    let := h
    exact exists_sigmaLocallyFiniteBasis (X := X)
  · exact HasSigmaLocallyFiniteBasis.metrizableSpace

/-- A compatible metric constructed from the basis criterion. Its topology is
definitionally the supplied topology, even when a layer is uncountable. -/
@[instance_reducible]
noncomputable def compatibleMetric [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) : MetricSpace X :=
  let : MetrizableSpace X := h.metrizableSpace
  metrizableSpaceMetric X

theorem compatibleMetric_topology [T3Space X]
    (h : HasSigmaLocallyFiniteBasis X) :
    (compatibleMetric h).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace X› := by
  with_reducible_and_instances rfl

/-- The full criterion with the sigma locally finite basis expanded explicitly. -/
theorem metrizable_iff_sigmaLocallyFiniteBasis [T3Space X] :
    MetrizableSpace X ↔ ∃ B : ℕ → Set (Set X),
      (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
        IsTopologicalBasis (⋃ n, B n) := nagata_smirnov

/-- The full criterion expressed by existence of an actual metric whose induced
topology equals the given topology. -/
theorem compatible_metric_iff [T3Space X] :
    (∃ m : MetricSpace X,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X›) ↔
      HasSigmaLocallyFiniteBasis X := by
  constructor
  · rintro ⟨m, hm⟩
    let : MetricSpace X := m.replaceTopology hm.symm
    exact exists_sigmaLocallyFiniteBasis (X := X)
  · intro h
    exact ⟨compatibleMetric h, compatibleMetric_topology h⟩

end NagataSmirnov

/-!
# A sigma locally finite basis from a point finite metrizable cover

Refine the cover of all local metric balls at each reciprocal natural radius.
At a fixed point, only finitely many patches contain it, so a common radius
works in all these patches. The triangle inequality controls any refining set
that contains the point.

Reference: James R. Munkres, *Topology*, second edition, Section 42,
Theorem 42.1, pages 261–262.
-/

@[expose] public section

open Set TopologicalSpace Metric

namespace Smirnov

variable {X I : Type*} [TopologicalSpace X]

/-- A paracompact space with a point finite open cover by metrizable patches
admits a sigma locally finite basis. Neither the cover nor a basis layer is
required to be countable. -/
theorem exists_sigmaLocallyFiniteBasis_of_pointFinite_open_cover [ParacompactSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hpf : ∀ x, {i | x ∈ U i}.Finite) (hmet : ∀ i, MetrizableSpace (U i)) :
    NagataSmirnov.HasSigmaLocallyFiniteBasis X := by
  classical
  let : ∀ i, MetrizableSpace (U i) := hmet
  let : ∀ i, MetricSpace (U i) := fun i => metrizableSpaceMetric (U i)
  let r (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
  have hr : ∀ n, 0 < r n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  let C (n : ℕ) (p : Σ i, U i) : Set X := Subtype.val '' ball p.2 (r n)
  have hCo : ∀ n p, IsOpen (C n p) := fun n p =>
    (hU p.1).isOpenMap_subtype_val _ isOpen_ball
  have hCc : ∀ n, ⋃ p, C n p = univ := by
    intro n
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨i, hxi⟩ := iUnion_eq_univ_iff.mp hcover x
    exact ⟨⟨i, ⟨x, hxi⟩⟩, ⟨⟨x, hxi⟩, mem_ball_self (hr n), rfl⟩⟩
  choose D hDo hDc hDf hDsub using fun n => precise_refinement (C n) (hCo n) (hCc n)
  refine ⟨fun n => range (D n), fun n => (hDf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro W hW
    obtain ⟨n, p, rfl⟩ := mem_iUnion.mp hW
    exact hDo n p
  · intro x G hxG hG
    let S : Set I := {i | x ∈ U i}
    have hS : S.Finite := hpf x
    let : Fintype S := hS.fintype
    have hball : ∀ i : S, ∃ δ > (0 : ℝ),
        ball (⟨x, i.2⟩ : U i.1) δ ⊆ Subtype.val ⁻¹' G := by
      intro i
      exact Metric.isOpen_iff.mp (hG.preimage continuous_subtype_val) _ hxG
    choose δ hδ hδsub using hball
    choose k hk using fun i : S => exists_nat_one_div_lt (half_pos (hδ i))
    obtain ⟨n, hn⟩ := (finite_range k).bddAbove
    have hnrad : ∀ i : S, r n < δ i / 2 := by
      intro i
      have hkn : k i ≤ n := hn (mem_range_self i)
      have hrad : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (k i + 1 : ℝ) :=
        one_div_le_one_div_of_le (Nat.cast_add_one_pos (k i))
          (by exact_mod_cast Nat.add_le_add_right hkn 1)
      exact hrad.trans_lt (hk i)
    obtain ⟨p, hxp⟩ := iUnion_eq_univ_iff.mp (hDc n) x
    obtain ⟨z, hzc, hzx⟩ := hDsub n p hxp
    have hxi : x ∈ U p.1 := hzx ▸ z.2
    have hzEq : z = (⟨x, hxi⟩ : U p.1) := Subtype.ext hzx
    rw [hzEq] at hzc
    let ix : S := ⟨p.1, hxi⟩
    refine ⟨D n p, mem_iUnion_of_mem n (mem_range_self p), hxp, ?_⟩
    intro y hy
    obtain ⟨w, hwc, rfl⟩ := hDsub n p hy
    apply hδsub ix
    rw [mem_ball] at hwc hzc ⊢
    calc
      dist w (⟨x, hxi⟩ : U p.1) ≤ dist w p.2 + dist p.2 ⟨x, hxi⟩ :=
        dist_triangle _ _ _
      _ = dist w p.2 + dist (⟨x, hxi⟩ : U p.1) p.2 := by rw [dist_comm p.2]
      _ < r n + r n := add_lt_add hwc hzc
      _ < δ ix := (add_lt_add (hnrad ix) (hnrad ix)).trans_eq (add_halves (δ ix))

end Smirnov

/-!
# Smirnov's local-to-global metrization theorem

A space is metrizable exactly when it is Hausdorff, paracompact, and locally
metrizable. Local patches and locally finite basis layers have arbitrary size.

References: Munkres, *Topology*, second edition, Theorem 42.1, pp. 261–262;
Sakai, *Geometric Aspects of General Topology*, second-edition manuscript,
Proposition 2.6.8(4), with the Hausdorff convention of Section 2.6.
-/

@[expose] public section

open Set TopologicalSpace

namespace Smirnov

variable {X I : Type*} [TopologicalSpace X]

/-- Every point has an open neighborhood whose inherited topology is metrizable. -/
def LocallyMetrizable (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U

theorem locallyMetrizable_of_metrizable [MetrizableSpace X] : LocallyMetrizable X := by
  intro x
  exact ⟨univ, isOpen_univ, mem_univ x, inferInstance⟩

/-- An arbitrary open cover by metrizable subspaces suffices in a paracompact
Hausdorff space. Neither the cover nor its members need be second countable. -/
theorem metrizable_of_open_cover [T2Space X] [ParacompactSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (hmet : ∀ i, MetrizableSpace (U i)) : MetrizableSpace X := by
  classical
  obtain ⟨V, hVo, hVc, hVf, hVsub⟩ := precise_refinement U hU hcover
  have hVm : ∀ i, MetrizableSpace (V i) := by
    intro i
    let : MetrizableSpace (U i) := hmet i
    exact (Topology.IsEmbedding.inclusion (hVsub i)).metrizableSpace
  let : NormalSpace X := NormalSpace.of_paracompactSpace_r1Space (X := X)
  let : T3Space X := inferInstance
  exact (exists_sigmaLocallyFiniteBasis_of_pointFinite_open_cover
    V hVo hVc hVf.point_finite hVm).metrizableSpace

theorem LocallyMetrizable.metrizableSpace [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : MetrizableSpace X := by
  classical
  choose U hU hxU hmet using h
  exact metrizable_of_open_cover U hU
    (iUnion_eq_univ_iff.mpr fun x => ⟨x, hxU x⟩) hmet

/-- Smirnov's full criterion. Hausdorffness is explicit because Mathlib's
`ParacompactSpace` does not include it. -/
theorem metrizable_iff : MetrizableSpace X ↔
    T2Space X ∧ ParacompactSpace X ∧ LocallyMetrizable X := by
  constructor
  · intro h
    let : MetrizableSpace X := h
    let : MetricSpace X := metrizableSpaceMetric X
    exact ⟨inferInstance, inferInstance, locallyMetrizable_of_metrizable⟩
  · rintro ⟨hT2, hP, hL⟩
    let : T2Space X := hT2
    let : ParacompactSpace X := hP
    exact hL.metrizableSpace

/-- The criterion with the local condition expanded in the statement. -/
theorem metrizable_iff_explicit : MetrizableSpace X ↔
    T2Space X ∧ ParacompactSpace X ∧
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U :=
  metrizable_iff

/-- On a Hausdorff locally metrizable space, paracompactness is precisely the
remaining condition for a compatible metric. -/
theorem metrizable_iff_paracompact [T2Space X] (h : LocallyMetrizable X) :
    MetrizableSpace X ↔ ParacompactSpace X := by
  constructor
  · intro hM
    exact (metrizable_iff.mp hM).2.1
  · intro hP
    let : ParacompactSpace X := hP
    exact h.metrizableSpace

/-- A metric whose topology is the given topology. -/
@[instance_reducible]
noncomputable def compatibleMetric [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : MetricSpace X := by
  let : MetrizableSpace X := h.metrizableSpace
  exact metrizableSpaceMetric X

theorem compatibleMetric_topology [T2Space X] [ParacompactSpace X]
    (h : LocallyMetrizable X) : (compatibleMetric h).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) := by
  with_reducible_and_instances rfl

/-- Smirnov's criterion expressed by existence of an actual compatible metric. -/
theorem compatible_metric_iff :
    (∃ m : MetricSpace X,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X›) ↔
      T2Space X ∧ ParacompactSpace X ∧ LocallyMetrizable X := by
  constructor
  · rintro ⟨m, hm⟩
    let : MetricSpace X := m.replaceTopology hm.symm
    exact metrizable_iff.mp inferInstance
  · rintro ⟨hT2, hP, hL⟩
    let : T2Space X := hT2
    let : ParacompactSpace X := hP
    exact ⟨compatibleMetric hL, compatibleMetric_topology hL⟩

end Smirnov
