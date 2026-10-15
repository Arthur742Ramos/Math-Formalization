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
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Maps.Basic

/-! Canonical-import-only statement file. The first four modules reuse registered
Nagata-Smirnov (PALOMAR-2026-10-14-000001 v1, source6aa68b2cb67719a187e64de29567443575eb560e).
The fifth reuses perfect paracompactness (PALOMAR-2026-10-13-000004 v1,
source984a610395e195b8d3ca0cd88282ef343e74d33d). Their substantive declarations
are unchanged. The new contribution starts at FiberNeighborhoods. -/

/- Included module: NagataSmirnovSupport/SigmaBasis.lean. Previously registered support; no new claim. -/
@[expose] public section

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


/- Included module: NagataSmirnovSupport/CompatibleMetric.lean. Previously registered support; no new claim. -/
@[expose] public section

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


/- Included module: NagataSmirnovSupport/MetricBasis.lean. Previously registered support; no new claim. -/
@[expose] public section

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


/- Included module: NagataSmirnovSupport/Metrization.lean. Previously registered support; no new claim. -/
@[expose] public section

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


/- Included module: PerfectParacompactSupport.lean. Previously registered support; no new claim. -/
@[expose] public section
open Set Filter Function Topology
universe u v w
namespace PerfectParacompact
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Closedness turns a fibre-containing open set into a neighbourhood in the target. -/
theorem fibre_neighbourhood {f : X → Y} (hc : IsClosedMap f) {y : Y}
    {U : Set X} (ho : IsOpen U) (hs : f ⁻¹' {y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  refine ⟨(f '' Uᶜ)ᶜ, (hc _ ho.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hs (by simpa using hxy))
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

/-- Perfect maps send arbitrary locally finite indexed families to locally finite families. -/
theorem locallyFinite_image {ι : Type w} {f : X → Y} (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) {C : ι → Set X} (hC : LocallyFinite C) :
    LocallyFinite (fun i => f '' C i) := by
  classical
  intro y
  choose U hUx hUf using fun x => hC.exists_mem_basis (nhds_basis_opens x)
  rcases (hk y).elim_finite_subcover U (fun x => (hUx x).2)
      (fun x _ => mem_iUnion.mpr ⟨x, (hUx x).1⟩) with ⟨T, hT⟩
  rcases fibre_neighbourhood hc (isOpen_iUnion fun x => isOpen_iUnion fun _ => (hUx x).2) hT
      with ⟨V, hVo, hyV, hVU⟩
  refine ⟨V, hVo.mem_nhds hyV, (T.finite_toSet.biUnion fun x _ => hUf x).subset ?_⟩
  rintro i ⟨z, ⟨x, hxC, rfl⟩, hxV⟩
  rcases mem_iUnion₂.mp (hVU hxV) with ⟨a, ha, hxa⟩
  exact mem_iUnion₂.mpr ⟨a, ha, x, hxC, hxa⟩

/-- A continuous closed map with compact fibres pulls paracompactness back.
Neither surjectivity nor separation hypotheses are needed. -/
theorem paracompact_preimage {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) [ParacompactSpace Y] : ParacompactSpace X := by
  classical
  constructor
  intro ι S hSo hS
  have hfinite : ∀ y : Y, ∃ T : Finset ι, f ⁻¹' {y} ⊆ ⋃ i ∈ T, S i :=
    fun y => (hk y).elim_finite_subcover S hSo (by rw [hS]; exact subset_univ _)
  choose T hT using hfinite
  choose V hVo hyV hVS using fun y => fibre_neighbourhood hc
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => hSo i) (hT y)
  rcases precise_refinement V hVo (iUnion_eq_univ_iff.mpr fun y => ⟨y, hyV y⟩)
      with ⟨W, hWo, hW, hWf, hWV⟩
  let R : (Σ y : Y, ↥(T y)) → Set X := fun a => S a.2 ∩ f ⁻¹' W a.1
  have hRo : ∀ a, IsOpen (R a) := fun a => (hSo _).inter ((hWo _).preimage hf)
  have hR : ⋃ a, R a = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases iUnion_eq_univ_iff.mp hW (f x) with ⟨y, hy⟩
    rcases mem_iUnion₂.mp (hVS y (hWV y hy)) with ⟨i, hi, hxi⟩
    exact ⟨⟨y, i, hi⟩, hxi, hy⟩
  have hRf : LocallyFinite R := by
    intro x
    rcases hWf (f x) with ⟨N, hN, hNf⟩
    refine ⟨f ⁻¹' N, hf.continuousAt hN,
      (hNf.biUnion fun y _ => finite_range (Sigma.mk y)).subset ?_⟩
    rintro ⟨y, i⟩ ⟨z, ⟨_, hzW⟩, hzN⟩
    exact mem_iUnion₂.mpr ⟨y, ⟨f z, hzW, hzN⟩, mem_range_self i⟩
  refine ⟨range R, Subtype.val, forall_subtype_range_iff.mpr hRo, ?_, hRf.on_range, ?_⟩
  · simpa only [iUnion_subtype, biUnion_range] using hR
  · exact forall_subtype_range_iff.mpr fun a => ⟨a.2, inter_subset_left⟩

/-- In a regular space, locally finite refinements need not initially be open.
Two refinements produce a locally finite open expansion of the first one. -/
theorem paracompact_of_refinements [RegularSpace Y]
    (H : ∀ (ι : Type v) (S : ι → Set Y), (∀ i, IsOpen (S i)) → (⋃ i, S i = univ) →
      ∃ (κ : Type v) (C : κ → Set Y), (⋃ i, C i = univ) ∧ LocallyFinite C ∧
        ∀ i, ∃ j, C i ⊆ S j) : ParacompactSpace Y := by
  classical
  constructor
  intro ι S hSo hS
  rcases H ι S hSo hS with ⟨κ, C, hC, hCf, hCS⟩
  choose a ha using hCS
  choose W hxW hWf using hCf
  choose R hRx hRW using fun x => (hasBasis_opens_closure x).mem_iff.mp (hxW x)
  rcases H Y R (fun x => (hRx x).2) (iUnion_eq_univ_iff.mpr fun x => ⟨x, (hRx x).1⟩)
      with ⟨γ, B, hB, hBf, hBR⟩
  choose b hb using hBR
  let D : γ → Set Y := fun j => closure (B j)
  have hDf : LocallyFinite D := hBf.closure
  have hDW : ∀ j, D j ⊆ W (b j) := fun j => (closure_mono (hb j)).trans (hRW _)
  let V : κ → Set Y := fun i => S (a i) ∩ (⋃ (j : γ) (_ : ¬ (C i ∩ W (b j)).Nonempty), D j)ᶜ
  have hVo : ∀ i, IsOpen (V i) := by
    intro i
    have hclosed : IsClosed (⋃ (j : γ) (_ : ¬ (C i ∩ W (b j)).Nonempty), D j) := by
      simpa only [iUnion_subtype, Function.comp_apply] using
        (hDf.comp_injective (Subtype.val_injective (p := fun j => ¬ (C i ∩ W (b j)).Nonempty))).isClosed_iUnion
          (fun j => isClosed_closure)
    exact (hSo _).inter hclosed.isOpen_compl
  have hCV : ∀ i, C i ⊆ V i := by
    intro i x hx
    refine ⟨ha i hx, ?_⟩
    rintro hxD
    rcases mem_iUnion₂.mp hxD with ⟨j, hj, hxD⟩
    exact hj ⟨x, hx, hDW j hxD⟩
  have hVf : LocallyFinite V := by
    intro x
    refine ⟨⋂ (j : γ) (_ : x ∉ D j), (D j)ᶜ,
      hDf.iInter_compl_mem_nhds (fun j => isClosed_closure) x,
      ((hDf.point_finite x).biUnion fun j _ => hWf (b j)).subset ?_⟩
    rintro i ⟨z, hzV, hzN⟩
    rcases iUnion_eq_univ_iff.mp hB z with ⟨j, hzB⟩
    have hzD : z ∈ D j := subset_closure hzB
    have hxD : x ∈ D j := by
      by_contra h
      exact (mem_iInter₂.mp hzN j h) hzD
    have hi : (C i ∩ W (b j)).Nonempty := by
      by_contra h
      exact hzV.2 (mem_iUnion₂.mpr ⟨j, h, hzD⟩)
    exact mem_iUnion₂.mpr ⟨j, hxD, hi⟩
  refine ⟨κ, V, hVo, ?_, hVf, fun i => ⟨a i, inter_subset_left⟩⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  rcases iUnion_eq_univ_iff.mp hC x with ⟨i, hi⟩
  exact ⟨i, hCV i hi⟩

/-- The regular-space locally finite refinement criterion, in both directions. -/
theorem paracompact_iff_refinements [RegularSpace Y] : ParacompactSpace Y ↔
    ∀ (ι : Type v) (S : ι → Set Y), (∀ i, IsOpen (S i)) → (⋃ i, S i = univ) →
      ∃ (κ : Type v) (C : κ → Set Y), (⋃ i, C i = univ) ∧ LocallyFinite C ∧
        ∀ i, ∃ j, C i ⊆ S j := by
  constructor
  · intro h ι S ho hS
    let _ := h
    rcases ParacompactSpace.locallyFinite_refinement ι S ho hS
      with ⟨κ, C, _, hC, hCf, hCS⟩
    exact ⟨κ, C, hC, hCf, hCS⟩
  · exact paracompact_of_refinements

/-- A closed continuous surjection takes normality to normality. -/
theorem normal_image {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hs : Surjective f) [NormalSpace X] : NormalSpace Y := by
  constructor
  intro A B hA hB hAB
  have hab : Disjoint (f ⁻¹' A) (f ⁻¹' B) := hAB.preimage f
  rcases normal_separation (hA.preimage hf) (hB.preimage hf) hab
      with ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩
  refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ,
    (hc _ hUo.isClosed_compl).isOpen_compl,
    (hc _ hVo.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hAU hy)
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hBV hy)
  · apply disjoint_left.mpr
    intro y hyU hyV
    rcases hs y with ⟨x, rfl⟩
    have hxU : x ∈ U := by
      by_contra h
      exact hyU ⟨x, h, rfl⟩
    have hxV : x ∈ V := by
      by_contra h
      exact hyV ⟨x, h, rfl⟩
    exact hUV.le_bot ⟨hxU, hxV⟩

/-- A perfect surjection sends paracompactness to a regular target. -/
theorem paracompact_image [RegularSpace Y] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) [ParacompactSpace X] : ParacompactSpace Y := by
  apply paracompact_of_refinements
  intro ι S hSo hS
  have hp : ⋃ i, f ⁻¹' S i = univ := by
    rw [← preimage_iUnion, hS, preimage_univ]
  rcases precise_refinement (fun i => f ⁻¹' S i) (fun i => (hSo i).preimage hf) hp
      with ⟨C, hCo, hC, hCf, hCS⟩
  refine ⟨ι, fun i => f '' C i, ?_, locallyFinite_image hc hk hCf, fun i => ⟨i, ?_⟩⟩
  · apply iUnion_eq_univ_iff.mpr
    intro y
    rcases hs y with ⟨x, rfl⟩
    rcases iUnion_eq_univ_iff.mp hC x with ⟨i, hi⟩
    exact ⟨i, x, hi, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hCS i hx

/-- A perfect surjection from a Hausdorff space preserves and reflects paracompactness.
No separation hypothesis is imposed on the target. -/
theorem paracompact_iff [T2Space X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    ParacompactSpace X ↔ ParacompactSpace Y := by
  constructor
  · intro h
    let _ := h
    let _ : T1Space Y := ⟨fun y => by
      rcases hs y with ⟨x, rfl⟩
      simpa only [image_singleton] using hc {x} isClosed_singleton⟩
    let _ : NormalSpace Y := normal_image hf hc hs
    exact paracompact_image hf hc hk hs
  · intro h
    let _ := h
    exact paracompact_preimage hf hc hk

/-- The perfect image of a paracompact Hausdorff space is paracompact Hausdorff.
The codomain has no assumed separation property. -/
theorem paracompact_t2_image [T2Space X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f)
    [ParacompactSpace X] : ParacompactSpace Y ∧ T2Space Y := by
  let _ : T1Space Y := ⟨fun y => by
    rcases hs y with ⟨x, rfl⟩
    simpa only [image_singleton] using hc {x} isClosed_singleton⟩
  let _ : NormalSpace Y := normal_image hf hc hs
  exact ⟨paracompact_image hf hc hk hs, inferInstance⟩

end PerfectParacompact


/- Included module: FiberNeighborhoods.lean. New proof development. -/
@[expose] public section

open Set Function Metric

namespace PerfectImage

variable {X Y : Type*}

/-- The values whose entire fiber lies in `U`. -/
def upperImage (f : X → Y) (U : Set X) : Set Y := (f '' Uᶜ)ᶜ

theorem mem_upperImage_iff (f : X → Y) (U : Set X) (y : Y) :
    y ∈ upperImage f U ↔ f ⁻¹' {y} ⊆ U := by
  constructor
  · intro hy x hx
    by_contra hxU
    exact hy ⟨x, hxU, mem_singleton_iff.mp hx⟩
  · intro h hy
    obtain ⟨x, hxU, hxy⟩ := hy
    exact hxU (h (show x ∈ f ⁻¹' {y} from hxy))

theorem preimage_upperImage_subset (f : X → Y) (U : Set X) :
    f ⁻¹' upperImage f U ⊆ U := by
  intro x hx
  exact (mem_upperImage_iff f U (f x)).mp hx rfl

section Topological

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem upperImage_isOpen {f : X → Y} (hc : IsClosedMap f)
    {U : Set X} (hU : IsOpen U) : IsOpen (upperImage f U) :=
  (hc _ hU.isClosed_compl).isOpen_compl

end Topological

section Metric

variable [MetricSpace X]

/-- The values whose entire fiber lies within distance `r` of the fiber at `y`. -/
def fiberNeighborhood (f : X → Y) (r : ℝ) (y : Y) : Set Y :=
  upperImage f (thickening r (f ⁻¹' {y}))

theorem mem_fiberNeighborhood_iff (f : X → Y) (r : ℝ) (y z : Y) :
    z ∈ fiberNeighborhood f r y ↔ f ⁻¹' {z} ⊆ thickening r (f ⁻¹' {y}) :=
  mem_upperImage_iff f _ z

theorem fiberNeighborhood_isOpen [TopologicalSpace Y] {f : X → Y}
    (hc : IsClosedMap f) (r : ℝ) (y : Y) :
    IsOpen (fiberNeighborhood f r y) :=
  upperImage_isOpen hc isOpen_thickening

theorem mem_fiberNeighborhood_self (f : X → Y) {r : ℝ} (hr : 0 < r) (y : Y) :
    y ∈ fiberNeighborhood f r y :=
  (mem_fiberNeighborhood_iff f r y y).mpr (self_subset_thickening hr _)

/-- All sufficiently small fiber neighborhoods containing `y` are contained in
any prescribed open neighborhood of `y`. No separation assumption on the target
is needed for this estimate. -/
theorem exists_radius_star_subset [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f)
    (y : Y) {G : Set Y} (hG : IsOpen G) (hy : y ∈ G) :
    ∃ ε > (0 : ℝ), ∀ r, 0 < r → r < ε →
      ∀ z, y ∈ fiberNeighborhood f r z → fiberNeighborhood f r z ⊆ G := by
  have hFyG : f ⁻¹' {y} ⊆ f ⁻¹' G := by
    intro x hx
    change f x ∈ G
    rw [show f x = y from hx]
    exact hy
  obtain ⟨a, ha, hta⟩ := (hk y).exists_thickening_subset_open (hG.preimage hf) hFyG
  let V := fiberNeighborhood f (a / 2) y
  have hVo : IsOpen V := fiberNeighborhood_isOpen hc _ _
  have hyV : y ∈ V := mem_fiberNeighborhood_self f (half_pos ha) y
  have hFyV : f ⁻¹' {y} ⊆ f ⁻¹' V := by
    intro x hx
    change f x ∈ V
    rw [show f x = y from hx]
    exact hyV
  obtain ⟨δ, hδ, htδ⟩ := (hk y).exists_thickening_subset_open (hVo.preimage hf) hFyV
  refine ⟨min δ (a / 2), lt_min hδ (half_pos ha), ?_⟩
  intro r _hr hrε z hyz w hw
  have hrδ : r < δ := hrε.trans_le (min_le_left _ _)
  have hra : r < a / 2 := hrε.trans_le (min_le_right _ _)
  obtain ⟨x, hxy⟩ := hs y
  have hxF : x ∈ f ⁻¹' {y} := hxy
  obtain ⟨c, hcF, hxc⟩ := mem_thickening_iff.mp
    ((mem_fiberNeighborhood_iff f r z y).mp hyz hxF)
  have hcδ : c ∈ thickening δ (f ⁻¹' {y}) :=
    mem_thickening_iff.mpr ⟨x, hxF, by rw [dist_comm]; exact hxc.trans hrδ⟩
  have hzV : z ∈ V := by
    have hfc : f c ∈ V := htδ hcδ
    rw [show f c = z from hcF] at hfc
    exact hfc
  have hzTube : f ⁻¹' {z} ⊆ thickening (a / 2) (f ⁻¹' {y}) :=
    (mem_fiberNeighborhood_iff f (a / 2) y z).mp hzV
  obtain ⟨b, hbw⟩ := hs w
  have hbF : b ∈ f ⁻¹' {w} := hbw
  obtain ⟨d, hdF, hbd⟩ := mem_thickening_iff.mp
    ((mem_fiberNeighborhood_iff f r z w).mp hw hbF)
  obtain ⟨e, heF, hde⟩ := mem_thickening_iff.mp (hzTube hdF)
  have hbTube : b ∈ thickening a (f ⁻¹' {y}) := by
    apply mem_thickening_iff.mpr
    refine ⟨e, heF, ?_⟩
    calc
      dist b e ≤ dist b d + dist d e := dist_triangle _ _ _
      _ < r + a / 2 := add_lt_add hbd hde
      _ < a := (add_lt_add_of_lt_of_le hra le_rfl).trans_eq (add_halves a)
  have hfb : f b ∈ G := hta hbTube
  rw [hbw] at hfb
  exact hfb

end Metric
end PerfectImage


/- Included module: PerfectImage.lean. New proof development. -/
@[expose] public section

open Set Function TopologicalSpace Topology Metric

namespace PerfectImage

universe uImage vImage
variable {X : Type uImage} {Y : Type vImage} [TopologicalSpace X] [TopologicalSpace Y]

/-- Locally finite refinements of the compact-fiber metric neighborhood covers
form a basis. The target needs only paracompactness at this construction stage. -/
theorem sigmaLocallyFiniteBasis_image [MetrizableSpace X] [ParacompactSpace Y]
    {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    NagataSmirnov.HasSigmaLocallyFiniteBasis Y := by
  classical
  let : MetricSpace X := metrizableSpaceMetric X
  have hr : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ) := fun n =>
    div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hcover : ∀ n : ℕ, ⋃ y : Y, fiberNeighborhood f (1 / (n + 1 : ℝ)) y = univ := by
    intro n
    exact iUnion_eq_univ_iff.mpr fun y => ⟨y, mem_fiberNeighborhood_self f (hr n) y⟩
  choose V hVo hVc hVf hVs using fun n : ℕ =>
    precise_refinement (fiberNeighborhood f (1 / (n + 1 : ℝ)))
      (fiberNeighborhood_isOpen hc _) (hcover n)
  refine ⟨fun n => range (V n), fun n => (hVf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    rcases mem_iUnion.mp hU with ⟨n, y, rfl⟩
    exact hVo n y
  · intro y G hy hG
    obtain ⟨ε, hε, hεG⟩ := exists_radius_star_subset hf hc hk hs y hG hy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨z, hyz⟩ := iUnion_eq_univ_iff.mp (hVc n) y
    exact ⟨V n z, mem_iUnion.mpr ⟨n, mem_range_self z⟩, hyz,
      (hVs n z).trans (hεG _ (hr n) hn z (hVs n z hyz))⟩

/-- A continuous closed surjection with compact fibers from an arbitrary
metrizable space has a metrizable codomain. Target separation is derived. -/
theorem metrizable_image [MetrizableSpace X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    MetrizableSpace Y := by
  let : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨hP, hT⟩ := PerfectParacompact.paracompact_t2_image hf hc hk hs
  let : ParacompactSpace Y := hP
  let : T2Space Y := hT
  let : NormalSpace Y := PerfectParacompact.normal_image hf hc hs
  let : T3Space Y := inferInstance
  exact (sigmaLocallyFiniteBasis_image hf hc hk hs).metrizableSpace

/-- The same perfect-image theorem with Mathlib's proper-map interface. -/
theorem metrizable_image_of_proper [MetrizableSpace X] {f : X → Y}
    (hf : IsProperMap f) (hs : Surjective f) : MetrizableSpace Y :=
  metrizable_image hf.continuous hf.isClosedMap
    (fun _ => hf.isCompact_preimage isCompact_singleton) hs

/-- An actual metric inducing the codomain's original topology. -/
@[instance_reducible]
noncomputable def compatibleMetric [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) : MetricSpace Y := by
  let : MetrizableSpace Y := metrizable_image hf hc hk hs
  exact metrizableSpaceMetric Y

theorem compatibleMetric_topology [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) :
    (compatibleMetric hf hc hk hs).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Y) := by
  with_reducible_and_instances rfl

/-- The conclusion expressed without the `MetrizableSpace` class. -/
theorem exists_compatibleMetric [MetrizableSpace X] {f : X → Y}
    (hf : Continuous f) (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) :
    ∃ m : MetricSpace Y, m.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Y) :=
  ⟨compatibleMetric hf hc hk hs, compatibleMetric_topology hf hc hk hs⟩

end PerfectImage
