/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Foundations
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

open Set Topology TopologicalSpace Filter
open scoped Topology

universe u v

namespace Composants

variable {X : Type u} [tX : TopologicalSpace X]

/-- An open cover of the whole space, represented as a family of sets. -/
def IsOpenCover (ω : Set (Set X)) : Prop :=
  (∀ U ∈ ω, IsOpen U) ∧ ⋃₀ ω = univ

/-- A closed separator whose complementary open sides contain `A` and `B`. -/
def IsPartitionBetween (P A B : Set X) : Prop :=
  IsClosed P ∧ ∃ U V : Set X,
    IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Pᶜ ∧ A ⊆ U ∧ B ⊆ V

/-- The inverse images of an open target cover refine the ambient cover on `P`. -/
def IsOmegaMap (ω : Set (Set X)) {P : Set X} {Y : Type v} [_tY : TopologicalSpace Y]
    (f : P → Y) : Prop :=
  Continuous f ∧ ∃ γ : Set (Set Y), IsOpenCover γ ∧
    ∀ V ∈ γ, ∃ U ∈ ω, f ⁻¹' V ⊆ Subtype.val ⁻¹' U

/-- A continuum is nonempty, compact, connected, and Hausdorff. -/
def IsContinuum (Y : Type v) [_tY : TopologicalSpace Y] : Prop :=
  Nonempty Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧ T2Space Y

theorem partition_inter_bridge {P A B C : Set X} (hp : IsPartitionBetween P A B)
    (hc : IsConnected C) (ha : (C ∩ A).Nonempty) (hb : (C ∩ B).Nonempty) :
    (C ∩ P).Nonempty := by
  obtain ⟨_, U, V, hu, hv, hd, he, hau, hbv⟩ := hp
  by_contra hn
  have hcp : C ⊆ Pᶜ := by
    intro x hx hpx
    exact hn ⟨x, hx, hpx⟩
  have hcov : C ⊆ U ∪ V := by rwa [he]
  obtain ⟨a, haC, haA⟩ := ha
  obtain ⟨b, hbC, hbB⟩ := hb
  rcases hc.isPreconnected.subset_or_subset hu hv hd hcov with h | h
  · exact Set.disjoint_left.mp hd (h hbC) (hbv hbB)
  · exact Set.disjoint_left.mp hd (hau haA) (h haC)

theorem partition_nonempty [ConnectedSpace X] {P A B : Set X}
    (hp : IsPartitionBetween P A B) (ha : A.Nonempty) (hb : B.Nonempty) : P.Nonempty := by
  simpa using partition_inter_bridge hp isConnected_univ
    (by simpa using ha) (by simpa using hb)

/-- One proper subcontinuum can be avoided by a compact connected bridge between any two
nonempty open sets. This uses a different dense composant. -/
theorem bridge_avoiding [CompactSpace X] [T2Space X] [ConnectedSpace X]
    [Nontrivial X] [SecondCountableTopology X] (hi : IsIndecomposable X)
    {K U V : Set X} (hk : IsSubcontinuum K) (hproper : K ≠ univ)
    (hu : IsOpen U) (hv : IsOpen V) (hU : U.Nonempty) (hV : V.Nonempty) :
    ∃ C : Set X, IsSubcontinuum C ∧ Disjoint C K ∧
      (C ∩ U).Nonempty ∧ (C ∩ V).Nonempty := by
  classical
  obtain ⟨q, hq⟩ := hk.2.nonempty
  have hkq : K ⊆ composant q := fun _ hx => ⟨K, hk, hproper, hq, hx⟩
  have hne : composant q ≠ univ := by
    intro he
    have hm := isMeagre_composant hi q
    rw [he] at hm
    exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hm
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ composant q := by
    by_contra! h
    exact hne (Set.eq_univ_of_forall h)
  have hd : Disjoint (composant z) (composant q) := by
    rcases composants_eq_or_disjoint hi z q with he | hd
    · exact (hz (he ▸ mem_composant_self z)).elim
    · exact hd
  obtain ⟨a, haU, ha⟩ := (dense_composant z).inter_open_nonempty U hu hU
  obtain ⟨b, hbV, hb⟩ := (dense_composant z).inter_open_nonempty V hv hV
  obtain ⟨Ka, hKa, hpKa, hzKa, haKa⟩ := ha
  obtain ⟨Kb, hKb, hpKb, hzKb, hbKb⟩ := hb
  have hsub : Ka ∪ Kb ⊆ composant z := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨Ka, hKa, hpKa, hzKa, hx⟩
    · exact ⟨Kb, hKb, hpKb, hzKb, hx⟩
  refine ⟨Ka ∪ Kb, ⟨hKa.1.union hKb.1, hKa.2.union ⟨z, hzKa, hzKb⟩ hKb.2⟩,
    hd.mono hsub hkq, ⟨a, Or.inl haKa, haU⟩, ⟨b, Or.inr hbKb, hbV⟩⟩

end Composants

namespace Composants

variable {X : Type u} [mX : MetricSpace X]

/-- An auxiliary small-fiber condition; the final theorem uses open covers. -/
def HasSmallMap (P : Set X) (ε : ℝ) : Prop :=
  ∃ (Y : Type v) (tY : TopologicalSpace Y), @IsContinuum Y tY ∧
    ∃ f : P → Y, @Continuous P Y inferInstance tY f ∧ Function.Surjective f ∧
      ∀ x y : P, f x = f y → dist (x : X) (y : X) < ε

theorem compact_distance_gap {F G : Set X} (hf : IsCompact F) (hg : IsClosed G)
    (hd : Disjoint F G) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F, ∀ y ∈ G, δ < dist x y := by
  obtain ⟨r, hr, hb⟩ := Metric.exists_pos_forall_lt_edist hf hg hd
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  have h := hb x hx y hy
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
  exact lt_of_not_ge fun hge => h.not_ge (ENNReal.ofReal_le_ofReal hge)

/-- A Hausdorff (Vietoris) limit of partitions admitting maps with shrinking fibers is connected. -/
theorem small_map_limit_connected [CompactSpace X]
    (P : ℕ → NonemptyCompacts X) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hs : ∀ n, HasSmallMap.{u,v} (P n : Set X) (ε n))
    (K : NonemptyCompacts X) (hlim : Tendsto P atTop (𝓝 K)) :
    IsConnected (K : Set X) := by
  classical
  refine ⟨K.nonempty, ?_⟩
  by_contra hn
  rw [isPreconnected_closed_iff] at hn
  push Not at hn
  obtain ⟨s, t, hsc, htc, hcover, hsne, htne, hnone⟩ := hn
  let F : Set X := (K : Set X) ∩ s
  let G : Set X := (K : Set X) ∩ t
  have hf : IsCompact F := K.isCompact.inter_right hsc
  have hg : IsCompact G := K.isCompact.inter_right htc
  have hd : Disjoint F G := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hh : x ∈ (K : Set X) ∩ (s ∩ t) := ⟨hx.1, hx.2, hy.2⟩
    rw [hnone] at hh
    exact hh
  obtain ⟨r, hr, hgap⟩ := compact_distance_gap hf hg.isClosed hd
  let U := Metric.thickening (r / 3) F
  let V := Metric.thickening (r / 3) G
  have hu : IsOpen U := Metric.isOpen_thickening
  have hv : IsOpen V := Metric.isOpen_thickening
  have hFU : F ⊆ U := Metric.self_subset_thickening (by positivity) F
  have hGV : G ⊆ V := Metric.self_subset_thickening (by positivity) G
  have hUVgap : ∀ x ∈ U, ∀ y ∈ V, r / 3 < dist x y := by
    intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := Metric.mem_thickening_iff.mp hx
    obtain ⟨b, hb, hyb⟩ := Metric.mem_thickening_iff.mp hy
    have hab := hgap a ha b hb
    have hh := dist_triangle a x b
    have hh' := dist_triangle x y b
    rw [dist_comm a x] at hh
    linarith
  have hKcov : (K : Set X) ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxS | hxT
    · exact Or.inl (hFU ⟨hx, hxS⟩)
    · exact Or.inr (hGV ⟨hx, hxT⟩)
  have hKhitU : ((K : Set X) ∩ U).Nonempty := by
    obtain ⟨x, hxK, hxS⟩ := hsne
    exact ⟨x, hxK, hFU ⟨hxK, hxS⟩⟩
  have hKhitV : ((K : Set X) ∩ V).Nonempty := by
    obtain ⟨x, hxK, hxT⟩ := htne
    exact ⟨x, hxK, hGV ⟨hxK, hxT⟩⟩
  have hc : ∀ᶠ n in atTop, (P n : Set X) ⊆ U ∪ V :=
    hlim ((NonemptyCompacts.isOpen_subsets_of_isOpen (hu.union hv)).mem_nhds hKcov)
  have hhU : ∀ᶠ n in atTop, ((P n : Set X) ∩ U).Nonempty :=
    hlim ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hu).mem_nhds hKhitU)
  have hhV : ∀ᶠ n in atTop, ((P n : Set X) ∩ V).Nonempty :=
    hlim ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hv).mem_nhds hKhitV)
  have he : ∀ᶠ n in atTop, ε n < r / 3 := hε (Iio_mem_nhds (by positivity))
  obtain ⟨n, hcov, hhitU, hhitV, heps⟩ := (hc.and (hhU.and (hhV.and he))).exists
  obtain ⟨Y, tY, hY, f, hcont, hsurj, hsmall⟩ := hs n
  let _ : TopologicalSpace Y := tY
  let _ : ConnectedSpace Y := hY.2.2.1
  let _ : T2Space Y := hY.2.2.2
  let S : Set (P n) := Subtype.val ⁻¹' Vᶜ
  let T : Set (P n) := Subtype.val ⁻¹' Uᶜ
  have hS : IsCompact S := (hv.isClosed_compl.preimage continuous_subtype_val).isCompact
  have hT : IsCompact T := (hu.isClosed_compl.preimage continuous_subtype_val).isCompact
  have hSU : ∀ x ∈ S, (x : X) ∈ U := by
    intro x hx
    exact (hcov x.property).resolve_right hx
  have hTV : ∀ x ∈ T, (x : X) ∈ V := by
    intro x hx
    exact (hcov x.property).resolve_left hx
  have hdis : Disjoint (f '' S) (f '' T) := by
    rw [Set.disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hlow := hUVgap a (hSU a ha) b (hTV b hb)
    have hhigh := hsmall a b hba.symm
    linarith
  have himages : (univ : Set Y) ⊆ f '' S ∪ f '' T := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    by_cases hx : (x : X) ∈ U
    · exact Or.inl ⟨x, fun hvx => (by have := hUVgap x hx x hvx; rw [dist_self] at this; linarith), rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hSn : (f '' S).Nonempty := by
    obtain ⟨x, hxP, hxU⟩ := hhitU
    refine ⟨f ⟨x, hxP⟩, ⟨⟨x, hxP⟩, ?_, rfl⟩⟩
    intro hxV
    have hh := hUVgap x hxU x hxV
    rw [dist_self] at hh
    linarith
  have hTn : (f '' T).Nonempty := by
    obtain ⟨x, hxP, hxV⟩ := hhitV
    refine ⟨f ⟨x, hxP⟩, ⟨⟨x, hxP⟩, ?_, rfl⟩⟩
    intro hxU
    have hh := hUVgap x hxU x hxV
    rw [dist_self] at hh
    linarith
  obtain ⟨y, _, hyS, hyT⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
    (f '' S) (f '' T) (hS.image hcont).isClosed (hT.image hcont).isClosed himages
    (by simpa using hSn) (by simpa using hTn)
  exact Set.disjoint_left.mp hdis hyS hyT

theorem partition_avoids_left {P A B : Set X} (hp : IsPartitionBetween P A B) :
    P ⊆ Aᶜ := by
  obtain ⟨_, U, V, _, _, _, he, hau, _⟩ := hp
  intro x hx hxA
  have hh : x ∈ U ∪ V := Or.inl (hau hxA)
  rw [he] at hh
  exact hh hx

/-- The uniform shrinking-fiber obstruction underlying the open-cover statement. -/
theorem small_map_obstruction [CompactSpace X] [ConnectedSpace X]
    (hi : IsIndecomposable X) (A B : Set X) (hdis : Disjoint A B)
    (ha : (interior A).Nonempty) (hb : (interior B).Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : Set X,
      IsPartitionBetween P A B → ¬ HasSmallMap.{u,v} P ε := by
  classical
  obtain ⟨a, haI⟩ := ha
  obtain ⟨b, hbI⟩ := hb
  have hab : a ≠ b := by
    intro he
    exact Set.disjoint_left.mp hdis (interior_subset haI) (he ▸ interior_subset hbI)
  let _ : Nontrivial X := ⟨⟨a, b, hab⟩⟩
  by_contra hn
  have hbad : ∀ n : ℕ, ∃ P : Set X, IsPartitionBetween P A B ∧
      HasSmallMap.{u,v} P (1 / ((n : ℝ) + 1)) := by
    intro n
    by_contra! h
    exact hn ⟨1 / ((n : ℝ) + 1), by positivity, h⟩
  choose P hp hs using hbad
  let C : ℕ → NonemptyCompacts X := fun n =>
    ⟨⟨P n, (hp n).1.isCompact⟩, partition_nonempty (hp n)
      ⟨a, interior_subset haI⟩ ⟨b, interior_subset hbI⟩⟩
  obtain ⟨K, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq C
  have hK : IsConnected (K : Set X) := small_map_limit_connected (C ∘ φ)
    (fun n => 1 / ((φ n : ℝ) + 1))
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    (fun n => hs (φ n)) K hlim
  have hKA : (K : Set X) ⊆ (interior A)ᶜ := by
    apply (NonemptyCompacts.isClosed_subsets_of_isClosed isOpen_interior.isClosed_compl).mem_of_tendsto hlim
    exact Eventually.of_forall fun n x hx =>
      fun hxI => partition_avoids_left (hp (φ n)) hx (interior_subset hxI)
  have hproper : (K : Set X) ≠ univ := by
    intro he
    have hh := hKA (show a ∈ (K : Set X) by rw [he]; trivial)
    exact hh haI
  obtain ⟨D, hD, hdK, hDA, hDB⟩ := bridge_avoiding hi ⟨K.isCompact, hK⟩ hproper
    isOpen_interior isOpen_interior ⟨a, haI⟩ ⟨b, hbI⟩
  have hevent : ∀ᶠ n in atTop, (C (φ n) : Set X) ⊆ Dᶜ :=
    hlim ((NonemptyCompacts.isOpen_subsets_of_isOpen hD.1.isClosed.isOpen_compl).mem_nhds
      hdK.symm.subset_compl_right)
  obtain ⟨n, hnD⟩ := hevent.exists
  obtain ⟨x, hxD, hxP⟩ := partition_inter_bridge (hp (φ n)) hD.2
    (hDA.mono (inter_subset_inter_right _ interior_subset))
    (hDB.mono (inter_subset_inter_right _ interior_subset))
  exact hnD hxP hxD

/-- Todorov–Valov Theorem 3.3: one ambient cover obstructs every separator map onto a continuum.
The target continuum may live in an arbitrary universe independent of the ambient space. -/
theorem alexandroff_continua [cX : CompactSpace X] [cnX : ConnectedSpace X]
    (hi : IsIndecomposable X) (A B : Set X) (_hA : IsClosed A) (_hB : IsClosed B)
    (hdis : Disjoint A B) (ha : (interior A).Nonempty) (hb : (interior B).Nonempty) :
    ∃ ω : Set (Set X), IsOpenCover ω ∧ ∀ P : Set X, IsPartitionBetween P A B →
      ∀ (Y : Type v) [_tY : TopologicalSpace Y], IsContinuum Y →
        ∀ f : P → Y, Continuous f → Function.Surjective f → ¬ IsOmegaMap ω f := by
  classical
  obtain ⟨ε, hε, hobs⟩ := small_map_obstruction.{u,v} hi A B hdis ha hb
  let ω : Set (Set X) := Set.range (fun x : X => Metric.ball x (ε / 3))
  have hcover : IsOpenCover ω := by
    refine ⟨?_, Set.eq_univ_of_forall ?_⟩
    · rintro U ⟨x, rfl⟩
      exact Metric.isOpen_ball
    · intro x
      exact mem_sUnion.mpr ⟨Metric.ball x (ε / 3), ⟨x, rfl⟩,
        Metric.mem_ball_self (by positivity)⟩
  refine ⟨ω, hcover, ?_⟩
  intro P hp Y tY hY f hf hsurj hmap
  apply hobs P hp
  refine ⟨Y, tY, hY, f, hf, hsurj, ?_⟩
  intro x y hxy
  obtain ⟨_, γ, hγ, hrefine⟩ := hmap
  have hfx : f x ∈ ⋃₀ γ := by rw [hγ.2]; trivial
  obtain ⟨V, hV, hxV⟩ := mem_sUnion.mp hfx
  obtain ⟨U, hU, hsub⟩ := hrefine V hV
  obtain ⟨z, rfl⟩ := hU
  have hx : dist (x : X) z < ε / 3 := hsub hxV
  have hy : dist (y : X) z < ε / 3 := hsub (show f y ∈ V by rw [← hxy]; exact hxV)
  have hh := dist_triangle_right (x : X) (y : X) z
  linarith

end Composants
