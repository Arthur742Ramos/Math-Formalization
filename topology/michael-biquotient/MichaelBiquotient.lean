/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.WithTopology

/-!
# Michael's biquotient-map product and characterization theorems

Theorems 1.2 and 1.3 of Ernest Michael, "Bi-quotient maps and cartesian products
of quotient maps", Annales de l'Institut Fourier 18(2), 287–302 (1968).
The definition is the ordinary fiber-open-cover condition. Arbitrary indexed
products require no separation hypothesis. For Hausdorff targets, same-universe
tests suffice for both reverse implications; the forward implication is separately
polymorphic in the test-space universe.

The reverse witness is an actual Hausdorff paracompact topology on the underlying
target set. We obtain its filter through Proposition 2.2 and then refine to an
ultrafilter. This alternate route preserves every member of the failing fiber
cover and does not use the ambiguous cover-normalization sentence in Section 5.

These are classical results, not new mathematics. Michael acknowledges Hájek's
priority for the equivalent limit-lifting characterization and Theorem 1.3.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

universe u v w

namespace Michael

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous surjection is biquotient if every open cover of each fiber has
a finite subfamily whose images contain a neighborhood of the target point.
The family consists of open subsets of the whole domain, as in Michael 1.1. -/
def IsBiquotientMap (f : X → Y) : Prop :=
  Continuous f ∧ Surjective f ∧
    ∀ (y : Y) (𝒰 : Set (Set X)), (∀ U ∈ 𝒰, IsOpen U) →
      f ⁻¹' {y} ⊆ ⋃₀ 𝒰 →
      ∃ 𝒱 : Set (Set X), 𝒱.Finite ∧ 𝒱 ⊆ 𝒰 ∧ (f '' ⋃₀ 𝒱) ∈ 𝓝 y

/-- Michael's adherence lifting condition (Proposition 2.2), expressed using
proper filters and cluster points. -/
def LiftsClusterPoints (f : X → Y) : Prop :=
  ∀ (F : Filter Y) (y : Y), ClusterPt y F →
    ∃ x : X, f x = y ∧ ClusterPt x (comap f F)

theorem IsBiquotientMap.isQuotientMap {f : X → Y} (hf : IsBiquotientMap f) :
    IsQuotientMap f := by
  rw [isQuotientMap_iff]
  refine ⟨isCoinducing_iff.mpr (fun s => ⟨?_, fun hs => hs.preimage hf.1⟩), hf.2.1⟩
  intro hs
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨𝒱, hfin, hsub, hn⟩ := hf.2.2 y {f ⁻¹' s}
    (by simpa using hs) (by intro x hx; change f x = y at hx; simpa [hx] using hy)
  apply mem_of_superset hn
  rintro z ⟨x, hx, rfl⟩
  rcases mem_sUnion.mp hx with ⟨U, hU, hx⟩
  have hEq : U = f ⁻¹' s := by simpa using hsub hU
  rw [hEq] at hx
  exact hx

omit [TopologicalSpace Y] in
/-- For an ultrafilter, adherence to a pullback is equivalent to membership
of every image of a neighborhood. This retains finite-cylinder compatibility
in the arbitrary-product argument. -/
theorem clusterPt_comap_ultrafilter_iff {f : X → Y} {x : X} {U : Ultrafilter Y} :
    ClusterPt x (comap f U) ↔ (U : Filter Y) ≤ map f (𝓝 x) := by
  rw [ClusterPt, neBot_inf_comap_iff_map, inf_comm, Ultrafilter.inf_neBot_iff]

/-- Convergent-ultrafilter lifting, an intermediate condition proved equivalent
to the fiber-open-cover definition rather than used as its definition. -/
def LiftsUltrafilters (f : X → Y) : Prop :=
  ∀ (U : Ultrafilter Y) (y : Y), (U : Filter Y) ≤ 𝓝 y →
    ∃ x : X, f x = y ∧ ClusterPt x (comap f U)

theorem liftsClusterPoints_iff_liftsUltrafilters {f : X → Y} :
    LiftsClusterPoints f ↔ LiftsUltrafilters f := by
  constructor
  · intro h U y hy
    exact h U y (ClusterPt.of_le_nhds hy)
  · intro h F y hy
    obtain ⟨U, hUF, hUy⟩ := clusterPt_iff_ultrafilter.mp hy
    obtain ⟨x, hxy, hx⟩ := h U y hUy
    exact ⟨x, hxy, hx.mono (comap_mono hUF)⟩

theorem IsBiquotientMap.liftsUltrafilters {f : X → Y} (hf : IsBiquotientMap f) :
    LiftsUltrafilters f := by
  intro U y hUy
  by_contra h
  have hn : ∀ x, f x = y → ¬ ClusterPt x (comap f U) := by
    intro x hx hc
    exact h ⟨x, hx, hc⟩
  let 𝒰 : Set (Set X) := {V | IsOpen V ∧ f '' V ∉ U}
  have hcov : f ⁻¹' {y} ⊆ ⋃₀ 𝒰 := by
    intro x hx
    have hx' : f x = y := by simpa using hx
    have hn' := hn x hx'
    rw [clusterPt_comap_ultrafilter_iff] at hn'
    change ¬ ∀ s, s ∈ map f (𝓝 x) → s ∈ U at hn'
    push Not at hn'
    obtain ⟨t, ht, htu⟩ := hn'
    obtain ⟨s, hs, hst⟩ := mem_map_iff_exists_image.mp ht
    obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.mp hs
    refine mem_sUnion.mpr ⟨V, ⟨hVo, ?_⟩, hxV⟩
    intro hVU
    exact htu (mem_of_superset hVU ((image_mono hVs).trans hst))
  obtain ⟨𝒱, hfin, hsub, hn⟩ := hf.2.2 y 𝒰 (fun V hV => hV.1) hcov
  have himg : f '' ⋃₀ 𝒱 ∈ U := hUy hn
  rw [image_sUnion] at himg
  obtain ⟨t, ht, htU⟩ := (U.finite_sUnion_mem_iff (hfin.image (image f))).mp himg
  obtain ⟨V, hV, rfl⟩ := ht
  have hVU : f '' V ∈ U := htU
  exact (hsub hV).2 hVU

/-- The filter of complements of finite unions of images of cover members.
This is used only to prove the bridge from ordinary covers. -/
def finiteCoverFilter (f : X → Y) (𝒰 : Set (Set X)) : Filter Y where
  sets := {s | ∃ 𝒱 : Set (Set X), 𝒱.Finite ∧ 𝒱 ⊆ 𝒰 ∧ (f '' ⋃₀ 𝒱)ᶜ ⊆ s}
  univ_sets := ⟨∅, finite_empty, empty_subset _, subset_univ _⟩
  sets_of_superset := by
    rintro s t ⟨𝒱, hfin, hsub, hs⟩ hst
    exact ⟨𝒱, hfin, hsub, hs.trans hst⟩
  inter_sets := by
    rintro s t ⟨𝒱, hVfin, hVsub, hs⟩ ⟨𝒲, hWfin, hWsub, ht⟩
    refine ⟨𝒱 ∪ 𝒲, hVfin.union hWfin, union_subset hVsub hWsub, ?_⟩
    rw [sUnion_union, image_union, compl_union]
    exact inter_subset_inter hs ht

omit [TopologicalSpace X] in
theorem finiteCoverFilter_clusterPt {f : X → Y} {𝒰 : Set (Set X)} {y : Y}
    (hbad : ∀ 𝒱 : Set (Set X), 𝒱.Finite → 𝒱 ⊆ 𝒰 → f '' ⋃₀ 𝒱 ∉ 𝓝 y) :
    ClusterPt y (finiteCoverFilter f 𝒰) := by
  apply clusterPt_iff_nonempty.mpr
  rintro N hN s ⟨𝒱, hfin, hsub, hs⟩
  have hnsub : ¬ N ⊆ f '' ⋃₀ 𝒱 := fun h => hbad 𝒱 hfin hsub (mem_of_superset hN h)
  obtain ⟨z, hzN, hzV⟩ := not_subset.mp hnsub
  exact ⟨z, hzN, hs hzV⟩

theorem isBiquotientMap_iff_liftsClusterPoints {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) :
    IsBiquotientMap f ↔ LiftsClusterPoints f := by
  constructor
  · intro hf
    exact liftsClusterPoints_iff_liftsUltrafilters.mpr hf.liftsUltrafilters
  · intro hlift
    refine ⟨hcont, hsurj, ?_⟩
    intro y 𝒰 hopen hcover
    by_contra h
    push Not at h
    obtain ⟨x, hxy, hx⟩ := hlift (finiteCoverFilter f 𝒰) y
      (finiteCoverFilter_clusterPt h)
    obtain ⟨V, hVU, hxV⟩ := mem_sUnion.mp (hcover (by simpa using hxy))
    have hcompl : (f '' V)ᶜ ∈ finiteCoverFilter f 𝒰 :=
      ⟨{V}, finite_singleton V, singleton_subset_iff.mpr hVU, by simp⟩
    obtain ⟨z, hzV, hzcompl⟩ := clusterPt_iff_nonempty.mp hx
      (hopen V hVU |>.mem_nhds hxV) (preimage_mem_comap hcompl)
    exact hzcompl (mem_image_of_mem f hzV)

theorem isBiquotientMap_iff_liftsUltrafilters {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) :
    IsBiquotientMap f ↔ LiftsUltrafilters f :=
  (isBiquotientMap_iff_liftsClusterPoints hcont hsurj).trans
    liftsClusterPoints_iff_liftsUltrafilters

/-- Michael 1.2: arbitrary indexed products preserve biquotient maps, without
any separation hypothesis on domain or target. -/
theorem IsBiquotientMap.piMap {ι : Type w} {A : ι → Type u} {B : ι → Type v}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    {f : ∀ i, A i → B i} (hf : ∀ i, IsBiquotientMap (f i)) :
    IsBiquotientMap (Pi.map f) := by
  have hc : Continuous (Pi.map f) := continuous_pi fun i => (hf i).1.comp (continuous_apply i)
  have hs : Surjective (Pi.map f) := by
    intro y
    choose x hx using fun i => (hf i).2.1 (y i)
    exact ⟨x, funext hx⟩
  apply (isBiquotientMap_iff_liftsUltrafilters hc hs).mpr
  intro U y hUy
  have hcoord : ∀ i, ∃ x : A i, f i x = y i ∧
      ClusterPt x (comap (f i) (U.map (Function.eval i))) := by
    intro i
    apply (hf i).liftsUltrafilters
    exact (continuous_apply i).continuousAt.tendsto.comp hUy
  choose x hx hcluster using hcoord
  refine ⟨x, funext hx, clusterPt_comap_ultrafilter_iff.mpr ?_⟩
  rw [nhds_pi, map_piMap_pi (Eventually.of_forall fun i => (hf i).2.1)]
  apply le_iInf
  intro i
  apply map_le_iff_le_comap.mp
  exact clusterPt_comap_ultrafilter_iff.mp (hcluster i)

theorem IsBiquotientMap.prodMap {Z : Type w} {W : Type*}
    [TopologicalSpace Z] [TopologicalSpace W] {f : X → Y} {g : Z → W}
    (hf : IsBiquotientMap f) (hg : IsBiquotientMap g) :
    IsBiquotientMap (Prod.map f g) := by
  apply (isBiquotientMap_iff_liftsUltrafilters (hf.1.prodMap hg.1)
    (hf.2.1.prodMap hg.2.1)).mpr
  intro U y hUy
  obtain ⟨x, hxy, hx⟩ := hf.liftsUltrafilters (U.map Prod.fst) y.1
    ((continuous_fst.continuousAt.tendsto).comp hUy)
  obtain ⟨z, hzy, hz⟩ := hg.liftsUltrafilters (U.map Prod.snd) y.2
    ((continuous_snd.continuousAt.tendsto).comp hUy)
  refine ⟨(x, z), Prod.ext hxy hzy, clusterPt_comap_ultrafilter_iff.mpr ?_⟩
  rw [nhds_prod_eq, ← Filter.prod_map_map_eq', Filter.prod_eq_inf]
  exact le_inf (map_le_iff_le_comap.mp (clusterPt_comap_ultrafilter_iff.mp hx))
    (map_le_iff_le_comap.mp (clusterPt_comap_ultrafilter_iff.mp hz))

theorem isBiquotientMap_id : IsBiquotientMap (id : X → X) := by
  apply (isBiquotientMap_iff_liftsUltrafilters continuous_id surjective_id).mpr
  intro U x hx
  exact ⟨x, rfl, by rw [Filter.comap_id]; exact ClusterPt.of_le_nhds hx⟩

/-- The forward part of Michael 1.3 is polymorphic in the test-space universe. -/
theorem IsBiquotientMap.prod_id_isQuotientMap {f : X → Y} (hf : IsBiquotientMap f)
    (Z : Type w) [TopologicalSpace Z] : IsQuotientMap (Prod.map f (id : Z → Z)) :=
  (hf.prodMap isBiquotientMap_id).isQuotientMap

/-- The filter topology with one potentially non-isolated point. A set is open
exactly when containing the distinguished point forces membership in `F`. -/
@[instance_reducible]
def onePointTopology {α : Type*} (F : Filter α) (p : α) : TopologicalSpace α where
  IsOpen s := p ∈ s → s ∈ F
  isOpen_univ := fun _ => univ_mem
  isOpen_inter s t hs ht hp := inter_mem (hs hp.1) (ht hp.2)
  isOpen_sUnion S hS hp := by
    obtain ⟨s, hsS, hps⟩ := mem_sUnion.mp hp
    exact mem_of_superset (hS s hsS hps) (subset_sUnion_of_mem hsS)

theorem onePoint_isOpen {α : Type*} {F : Filter α} {p : α} {s : Set α} :
    IsOpen[onePointTopology F p] s ↔ (p ∈ s → s ∈ F) := Iff.rfl

theorem onePoint_singleton_open {α : Type*} (F : Filter α) {p z : α} (hz : z ≠ p) :
    IsOpen[onePointTopology F p] ({z} : Set α) := by
  intro hp
  exact False.elim (hz (mem_singleton_iff.mp hp).symm)

theorem onePoint_t2 {α : Type*} (F : Filter α) (p : α)
    (hsingle : ∀ z : α, ({z} : Set α)ᶜ ∈ F) :
    @T2Space α (onePointTopology F p) := by
  let := onePointTopology F p
  constructor
  intro x z hxz
  by_cases hx : x = p
  · subst x
    refine ⟨{z}ᶜ, {z}, ?_, onePoint_singleton_open F hxz.symm, ?_, by simp, ?_⟩
    · exact fun _ => hsingle z
    · simpa using hxz
    · exact disjoint_compl_left
  · by_cases hz : z = p
    · subst z
      refine ⟨{x}, {x}ᶜ, onePoint_singleton_open F hx, ?_, by simp, ?_, ?_⟩
      · exact fun _ => hsingle x
      · simpa using Ne.symm hx
      · exact disjoint_compl_right
    · exact ⟨{x}, {z}, onePoint_singleton_open F hx, onePoint_singleton_open F hz,
        by simp, by simp, disjoint_singleton.mpr hxz⟩

/-- An open cover of a space with one non-isolated point is refined by one
cover member containing that point and the singletons outside that member. -/
theorem onePoint_paracompact {α : Type*} (F : Filter α) (p : α) :
    @ParacompactSpace α (onePointTopology F p) := by
  classical
  let := onePointTopology F p
  constructor
  intro ι S hopen hcover
  obtain ⟨i₀, hi₀⟩ := iUnion_eq_univ_iff.mp hcover p
  let O := S i₀
  let T : α → Set α := fun x => if x ∈ O then O else {x}
  have hTo : ∀ x, IsOpen (T x) := by
    intro x
    by_cases hx : x ∈ O
    · simpa [T, hx] using hopen i₀
    · have hxp : x ≠ p := fun h => hx (h ▸ hi₀)
      simpa [T, hx] using onePoint_singleton_open F hxp
  -- Index the repeated large set only once, using its range.
  refine ⟨Set.range T, Subtype.val, (fun ⟨V, hV⟩ => ?_), ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hV
    exact hTo x
  · rw [iUnion_eq_univ_iff]
    intro x
    exact ⟨⟨T x, ⟨x, rfl⟩⟩, by simp [T]; split_ifs <;> simp_all⟩
  · intro x
    by_cases hx : x ∈ O
    · refine ⟨O, (hopen i₀).mem_nhds hx, ?_⟩
      apply (finite_singleton (⟨O, ⟨p, by simp [T, O, hi₀]⟩⟩ : Set.range T)).subset
      rintro ⟨V, ⟨z, rfl⟩⟩ hV
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      by_cases hz : z ∈ O
      · simp [T, hz]
      · obtain ⟨a, haT, haO⟩ := hV
        simp only [T, hz, ite_false, mem_singleton_iff] at haT
        exact False.elim (hz (haT ▸ haO))
    · have hxp : x ≠ p := fun h => hx (h ▸ hi₀)
      refine ⟨{x}, (onePoint_singleton_open F (p := p) hxp).mem_nhds (by simp), ?_⟩
      apply (finite_singleton (⟨{x}, ⟨x, by simp [T, hx]⟩⟩ : Set.range T)).subset
      rintro ⟨V, ⟨z, rfl⟩⟩ hV
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      obtain ⟨a, haT, hax⟩ := hV
      have hax' : a = x := mem_singleton_iff.mp hax
      subst a
      by_cases hz : z ∈ O
      · exact False.elim (hx (by simpa [T, hz] using haT))
      · have hxz : x = z := by simpa [T, hz] using haT
        simp [T, hz, hxz]
  · rintro ⟨V, ⟨x, rfl⟩⟩
    by_cases hx : x ∈ O
    · exact ⟨i₀, by simp [T, hx, O]⟩
    · obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hcover x
      exact ⟨i, by simpa [T, hx] using singleton_subset_iff.mpr hi⟩

/-- A copy of the underlying target set carrying the actual witness topology. -/
abbrev Witness {α : Type*} (F : Filter α) (p : α) :=
  WithTopology α (onePointTopology F p)

def onePointHomeomorph {α : Type*} (F : Filter α) (p : α) :
    @Homeomorph α (Witness F p) (onePointTopology F p)
      (WithTopology.instTopologicalSpace α (onePointTopology F p)) := by
  letI := onePointTopology F p
  exact {
    toEquiv := (WithTopology.equiv α (onePointTopology F p)).symm
    continuous_toFun := WithTopology.continuous_toTopology _
    continuous_invFun := WithTopology.continuous_ofTopology _ }

theorem witness_paracompact {α : Type*} (F : Filter α) (p : α) :
    ParacompactSpace (Witness F p) := by
  let := onePointTopology F p
  let : ParacompactSpace α := onePoint_paracompact F p
  exact (onePointHomeomorph F p).paracompactSpace_iff.mp inferInstance

theorem witness_t2 {α : Type*} (F : Filter α) (p : α)
    (hsingle : ∀ z : α, ({z} : Set α)ᶜ ∈ F) : T2Space (Witness F p) := by
  let := onePointTopology F p
  let : T2Space α := onePoint_t2 F p hsingle
  exact (onePointHomeomorph F p).t2Space

theorem witness_isOpen {α : Type*} {F : Filter α} {p : α} {s : Set (Witness F p)} :
    IsOpen s ↔ (WithTopology.toTopology (onePointTopology F p) p ∈ s →
      s ∈ map (WithTopology.toTopology (onePointTopology F p)) F) := Iff.rfl

theorem witness_mem_nhds_point {α : Type*} {F : Filter α} {p : α} {s : Set (Witness F p)}
    (hs : s ∈ 𝓝 (WithTopology.toTopology (onePointTopology F p) p)) :
    s ∈ map (WithTopology.toTopology (onePointTopology F p)) F := by
  obtain ⟨V, hVs, hVo, hpV⟩ := mem_nhds_iff.mp hs
  exact mem_of_superset (witness_isOpen.mp hVo hpV) hVs

/-- Failure of biquotience yields a convergent ultrafilter whose pullback has
no cluster point anywhere in the domain. Hausdorffness is used here. -/
theorem exists_ultrafilter_no_cluster [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) (hbad : ¬ IsBiquotientMap f) :
    ∃ (U : Ultrafilter Y) (y : Y), (U : Filter Y) ≤ 𝓝 y ∧
      (∀ x : X, ¬ ClusterPt x (comap f U)) ∧ (∀ z : Y, ({z} : Set Y)ᶜ ∈ U) := by
  rw [isBiquotientMap_iff_liftsUltrafilters hcont hsurj] at hbad
  change ¬ ∀ (U : Ultrafilter Y) y, (U : Filter Y) ≤ 𝓝 y → ∃ x, f x = y ∧ ClusterPt x (comap f U) at hbad
  push Not at hbad
  obtain ⟨U, y, hUy, hno⟩ := hbad
  have hnoc : ∀ x : X, ¬ ClusterPt x (comap f U) := by
    intro x hx
    have hUfx : (U : Filter Y) ≤ 𝓝 (f x) :=
      (clusterPt_comap_ultrafilter_iff.mp hx).trans hcont.continuousAt
    have hxy : f x = y := t2_iff_ultrafilter.mp inferInstance U hUfx hUy
    exact hno x hxy hx
  refine ⟨U, y, hUy, hnoc, ?_⟩
  intro z
  apply Ultrafilter.compl_mem_iff_notMem.mpr
  intro hzU
  obtain ⟨x, rfl⟩ := hsurj z
  apply hnoc x
  apply clusterPt_comap_ultrafilter_iff.mpr
  calc
    (U : Filter Y) ≤ pure (f x) := le_pure_iff.mpr hzU
    _ = map f (pure x) := (map_pure f x).symm
    _ ≤ map f (𝓝 x) := map_mono (pure_le_nhds x)

/-- The diagonal with its distinguished point deleted is not closed, while
its inverse image is closed. This is the reverse witness for Michael 1.3. -/
theorem witness_not_quotient [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (U : Ultrafilter Y) (y : Y)
    (hUy : (U : Filter Y) ≤ 𝓝 y)
    (hnoc : ∀ x : X, ¬ ClusterPt x (comap f U))
    (hsingle : ∀ z : Y, ({z} : Set Y)ᶜ ∈ U) :
    ¬ IsQuotientMap (Prod.map f (id : Witness (U : Filter Y) y → _)) := by
  classical
  let Z := Witness (U : Filter Y) y
  let toZ : Y → Z := WithTopology.toTopology (onePointTopology (U : Filter Y) y)
  let fromZ : Z → Y := WithTopology.ofTopology
  let D : Set (Y × Z) := {q | q.1 = fromZ q.2 ∧ q.1 ≠ y}
  have hto : Tendsto toZ U (𝓝 (toZ y)) := by
    intro s hs
    exact witness_mem_nhds_point hs
  have hDnot : ¬ IsClosed D := by
    intro hD
    have hd : Tendsto (fun z : Y => (z, toZ z)) U (𝓝 (y, toZ y)) :=
      (show Tendsto id (U : Filter Y) (𝓝 y) from by
        change map id (U : Filter Y) ≤ 𝓝 y
        rwa [Filter.map_id]).prodMk_nhds hto
    have hmem : ∀ᶠ z : Y in U, (z, toZ z) ∈ D := by
      filter_upwards [hsingle y] with z hz
      exact ⟨rfl, hz⟩
    have := hD.mem_of_tendsto hd hmem
    exact this.2 rfl
  have hpre : IsClosed ((Prod.map f (id : Z → Z)) ⁻¹' D) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    rintro ⟨x, z⟩ hp
    by_cases hzy : fromZ z = y
    · have hn := hnoc x
      rw [clusterPt_comap_ultrafilter_iff] at hn
      change ¬ ∀ s, s ∈ map f (𝓝 x) → s ∈ U at hn
      push Not at hn
      obtain ⟨s, hs, hsU⟩ := hn
      obtain ⟨V, hV, hVs⟩ := mem_map_iff_exists_image.mp hs
      obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.mp hV
      have hWU : (f '' W)ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr
        (fun h => hsU (mem_of_superset h ((image_mono hWV).trans hVs)))
      let N : Set Z := fromZ ⁻¹' ({y} ∪ (f '' W)ᶜ)
      have hNo : IsOpen N := by
        apply witness_isOpen.mpr
        intro _
        change ({y} ∪ (f '' W)ᶜ) ∈ U
        exact mem_of_superset hWU (subset_union_right)
      apply mem_of_superset (prod_mem_nhds (hWo.mem_nhds hxW) (hNo.mem_nhds ?_))
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ hD
        change f a = fromZ b ∧ f a ≠ y at hD
        rcases hb with hb | hb
        · exact hD.2 (hD.1.trans (mem_singleton_iff.mp hb))
        · exact hb (hD.1 ▸ mem_image_of_mem f ha)
      · change fromZ z ∈ {y} ∪ (f '' W)ᶜ
        exact Or.inl (mem_singleton_iff.mpr hzy)
    · have hfxz : f x ≠ fromZ z := by
        intro h
        exact hp ⟨h, fun hxy => hzy (h.symm.trans hxy)⟩
      have hzo : IsOpen ({z} : Set Z) := by
        apply witness_isOpen.mpr
        intro hpz
        have hpy : y = fromZ z := congr_arg fromZ (mem_singleton_iff.mp hpz)
        exact False.elim (hzy hpy.symm)
      have hfo : IsOpen (f ⁻¹' ({fromZ z} : Set Y)ᶜ) :=
        isClosed_singleton.isOpen_compl.preimage hcont
      apply mem_of_superset (prod_mem_nhds (hfo.mem_nhds ?_) (hzo.mem_nhds (by simp)))
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ hD
        have hbz : b = z := mem_singleton_iff.mp hb
        change f a = fromZ b ∧ f a ≠ y at hD
        exact ha (mem_singleton_iff.mpr (hD.1.trans (congr_arg fromZ hbz)))
      · simpa using hfxz
  intro hq
  exact hDnot (hq.isCoinducing.isClosed_preimage.mp hpre)

/-- An explicit Hausdorff paracompact counterexample, on a copy of the
underlying target set, for every non-biquotient continuous surjection. -/
theorem exists_t2_paracompact_counterexample [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) (hbad : ¬ IsBiquotientMap f) :
    ∃ (U : Ultrafilter Y) (y : Y), T2Space (Witness (U : Filter Y) y) ∧
      ParacompactSpace (Witness (U : Filter Y) y) ∧
      ¬ IsQuotientMap (Prod.map f (id : Witness (U : Filter Y) y → _)) := by
  obtain ⟨U, y, hUy, hnoc, hsingle⟩ := exists_ultrafilter_no_cluster hcont hsurj hbad
  exact ⟨U, y, witness_t2 U y hsingle, witness_paracompact U y,
    witness_not_quotient hcont U y hUy hnoc hsingle⟩

/-- Same-universe paracompact tests suffice because the reverse witness is a
new topology on the underlying set of `Y`. No Hausdorff condition is imposed
on the quantified test spaces. -/
theorem isBiquotientMap_iff_paracompact_tests [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) :
    IsBiquotientMap f ↔
      ∀ (Z : Type v) [TopologicalSpace Z] [ParacompactSpace Z],
        IsQuotientMap (Prod.map f (id : Z → Z)) := by
  constructor
  · intro hf Z _ _
    exact hf.prod_id_isQuotientMap Z
  · intro htest
    by_contra hbad
    obtain ⟨U, y, hUy, hnoc, hsingle⟩ := exists_ultrafilter_no_cluster hcont hsurj hbad
    let : ParacompactSpace (Witness (U : Filter Y) y) := witness_paracompact U y
    exact witness_not_quotient hcont U y hUy hnoc hsingle (htest (Witness (U : Filter Y) y))

/-- The full three-way equivalence of Michael 1.3, with same-universe tests
for the reverse implications and a separately polymorphic forward theorem. -/
theorem isBiquotientMap_iff_all_tests [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) :
    IsBiquotientMap f ↔ ∀ (Z : Type v) [TopologicalSpace Z],
      IsQuotientMap (Prod.map f (id : Z → Z)) := by
  constructor
  · intro hf Z _
    exact hf.prod_id_isQuotientMap Z
  · intro htest
    apply (isBiquotientMap_iff_paracompact_tests hcont hsurj).mpr
    intro Z _ _
    exact htest Z

theorem all_tests_iff_paracompact_tests [T2Space Y] {f : X → Y}
    (hcont : Continuous f) (hsurj : Surjective f) :
    (∀ (Z : Type v) [TopologicalSpace Z], IsQuotientMap (Prod.map f (id : Z → Z))) ↔
      ∀ (Z : Type v) [TopologicalSpace Z] [ParacompactSpace Z],
        IsQuotientMap (Prod.map f (id : Z → Z)) :=
  (isBiquotientMap_iff_all_tests hcont hsurj).symm.trans
    (isBiquotientMap_iff_paracompact_tests hcont hsurj)

end Michael
