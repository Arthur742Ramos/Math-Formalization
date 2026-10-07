/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import OrderArc
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.IntermediateValue
@[expose] public section
open Set Topology TopologicalSpace
universe u v
namespace WhitneyReversibility
variable {X : Type u} [mX : MetricSpace X] [cX : CompactSpace X]

/-- Nonempty compact connected sets with the induced Vietoris topology. -/
abbrev Continuum (X : Type u) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X)}

instance : CompactSpace (Continuum X) :=
  isCompact_iff_compactSpace.mp OrderArcs.isClosed_connected_values.isCompact

def singleton (x : X) : Continuum X := ⟨{x}, isConnected_singleton⟩
def whole [cnX : ConnectedSpace X] : Continuum X :=
  ⟨⟨⟨univ, isCompact_univ⟩, Set.univ_nonempty⟩, isConnected_univ⟩

/-- Literal continuity, singleton normalization and strict inclusion increase. -/
def IsWhitneyMap (μ : Continuum X → ℝ) : Prop :=
  Continuous μ ∧ (∀ x, μ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val < B.val → μ A < μ B

/-- Literal continuity, singleton normalization and weak inclusion increase. -/
def IsSizeMap (σ : Continuum X → ℝ) : Prop :=
  Continuous σ ∧ (∀ x, σ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val ≤ B.val → σ A ≤ σ B

omit [CompactSpace X] in
theorem IsWhitneyMap.isSizeMap {μ : Continuum X → ℝ} (hμ : IsWhitneyMap μ) :
    IsSizeMap μ := by
  refine ⟨hμ.1, hμ.2.1, ?_⟩
  intro A B hAB
  rcases eq_or_lt_of_le hAB with h | h
  · have : A = B := Subtype.ext h
    simp [this]
  · exact (hμ.2.2 A B h).le

/-- Order arcs with the equality case retained as a constant family. -/
theorem exists_order_path (A B : Continuum X) (hAB : A.val ≤ B.val) :
    ∃ α : unitInterval → Continuum X, Continuous α ∧ α 0 = A ∧ α 1 = B ∧
      Monotone (fun s => (α s).val) := by
  classical
  by_cases he : A.val = B.val
  · have he' : A = B := Subtype.ext he
    exact ⟨fun _ => A, continuous_const, rfl, he', fun _ _ _ => le_rfl⟩
  obtain ⟨α, hα, _, h0, h1, hc, hm⟩ := OrderArcs.exists_order_arc
    A.val B.val A.property B.property (lt_of_le_of_ne hAB he)
  exact ⟨fun s => ⟨α s, hc s⟩, hα.subtype_mk _, Subtype.ext h0,
    Subtype.ext h1, hm.monotone⟩

theorem connected_of_compact_surjection {A B : Type*}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B] [T2Space B]
    [ConnectedSpace B] (f : A → B) (hf : Continuous f)
    (hfs : Function.Surjective f) (hfib : ∀ b, IsConnected (f ⁻¹' {b})) :
    IsConnected (univ : Set A) := by
  have hq := hf.isClosedMap.isQuotientMap hf hfs
  simpa using hq.isCoinducing.isConnected_preimage_of_isClosed hfib
    isClosed_univ isConnected_univ


/-- A continuous vertically monotone square function has a connected level
when its bottom and top edges bound that level. Plateaus are allowed. -/
theorem connected_square_level (f : unitInterval × unitInterval → ℝ)
    (hf : Continuous f) (hm : ∀ s, Monotone (fun u => f (s, u))) (t : ℝ)
    (h0 : ∀ s, f (s, 0) ≤ t) (h1 : ∀ s, t ≤ f (s, 1)) :
    IsConnected {p | f p = t} := by
  let E := {p : unitInterval × unitInterval | f p = t}
  have hE : IsClosed E := isClosed_eq hf continuous_const
  let : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  let π : E → unitInterval := fun p => p.val.1
  have hπ : Continuous π := continuous_fst.comp continuous_subtype_val
  have hex : ∀ s : unitInterval, ∃ u, f (s, u) = t := fun s =>
    intermediate_value_univ₂ (hf.comp (continuous_const.prodMk continuous_id))
      continuous_const (h0 s) (h1 s)
  have hπs : Function.Surjective π := by
    intro s
    obtain ⟨u, hu⟩ := hex s
    exact ⟨⟨(s, u), hu⟩, rfl⟩
  have hfib : ∀ s, IsConnected (π ⁻¹' {s}) := by
    intro s
    let V : Set unitInterval := {u | f (s, u) = t}
    have hVo : V.OrdConnected := by
      constructor
      intro a ha b hb u hu
      exact le_antisymm (hb ▸ hm s hu.2) (ha ▸ hm s hu.1)
    have hVc : IsConnected V := ⟨hex s, hVo.isPreconnected⟩
    let g : V → E := fun u => ⟨(s, u.val), u.property⟩
    have hg : Continuous g :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have hi : g '' univ = π ⁻¹' {s} := by
      ext p
      constructor
      · rintro ⟨u, _, rfl⟩
        rfl
      · intro hp
        have hp' : p.val.1 = s := hp
        refine ⟨⟨p.val.2, ?_⟩, mem_univ _, ?_⟩
        · change f (s, p.val.2) = t
          simpa only [← hp', Prod.mk.eta] using (show f p.val = t from p.property)
        · apply Subtype.ext
          exact Prod.ext hp'.symm rfl
    let : ConnectedSpace V := Subtype.connectedSpace hVc
    rw [← hi]
    exact isConnected_univ.image g hg.continuousOn
  have hc := connected_of_compact_surjection π hπ hπs hfib
  have hi : Subtype.val '' (univ : Set E) = E := by simp
  change IsConnected E
  rw [← hi]
  exact hc.image Subtype.val continuous_subtype_val.continuousOn

def relativeLevel (σ : Continuum X → ℝ) (Y : Continuum X) (t : ℝ) :
    Set (Continuum X) := {K | K.val ≤ Y.val ∧ σ K = t}

theorem isCompact_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) (t : ℝ) : IsCompact (relativeLevel σ Y t) := by
  exact ((OrderArcs.isClosed_inclusion.preimage
    (continuous_subtype_val.prodMk continuous_const)).inter
    (isClosed_eq hσ.1 continuous_const)).isCompact

theorem exists_mem_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y)
    {x : X} (hx : x ∈ (Y.val : Set X)) :
    ∃ K ∈ relativeLevel σ Y t, x ∈ (K.val : Set X) := by
  have hs : (singleton x).val ≤ Y.val := Set.singleton_subset_iff.mpr hx
  obtain ⟨α, hα, hα0, hα1, hm⟩ := exists_order_path (singleton x) Y hs
  obtain ⟨u, hu⟩ := intermediate_value_univ₂ (a := (0 : unitInterval)) (b := 1) (g := fun _ => t) (hσ.1.comp hα)
    continuous_const (by simpa only [Function.comp_apply, hα0, hσ.2.1] using ht)
    (by simpa only [Function.comp_apply, hα1] using htY)
  refine ⟨α u, ⟨?_, hu⟩, ?_⟩
  · simpa only [hα1] using hm (show u ≤ 1 from unitInterval.le_one')
  · have h := hm (show 0 ≤ u from unitInterval.nonneg')
    change (α 0).val ≤ (α u).val at h
    rw [hα0] at h
    exact h (Set.mem_singleton x)

theorem connected_relativeLevel_pair {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y A B : Continuum X) (t : ℝ)
    (hA : A ∈ relativeLevel σ Y t) (hB : B ∈ relativeLevel σ Y t)
    {x : X} (hxA : x ∈ (A.val : Set X)) (hxB : x ∈ (B.val : Set X)) :
    ∃ S : Set (Continuum X), S ⊆ relativeLevel σ Y t ∧
      A ∈ S ∧ B ∈ S ∧ IsConnected S ∧
      ∀ K ∈ S, x ∈ (K.val : Set X) := by
  obtain ⟨α, hα, hα0, hα1, hmα⟩ := exists_order_path (singleton x) A
    (Set.singleton_subset_iff.mpr hxA)
  obtain ⟨β, hβ, hβ0, hβ1, hmβ⟩ := exists_order_path (singleton x) B
    (Set.singleton_subset_iff.mpr hxB)
  have hax : ∀ s, x ∈ ((α s).val : Set X) := by
    intro s
    have h := hmα (show 0 ≤ s from unitInterval.nonneg')
    change (α 0).val ≤ (α s).val at h
    rw [hα0] at h
    exact h (Set.mem_singleton x)
  have hbx : ∀ s, x ∈ ((β s).val : Set X) := by
    intro s
    have h := hmβ (show 0 ≤ s from unitInterval.nonneg')
    change (β 0).val ≤ (β s).val at h
    rw [hβ0] at h
    exact h (Set.mem_singleton x)
  let F : unitInterval × unitInterval → Continuum X := fun p =>
    ⟨(α p.1).val ⊔ (β p.2).val,
      (α p.1).property.union ⟨x, hax p.1, hbx p.2⟩ (β p.2).property⟩
  have hF : Continuous F :=
    ((continuous_subtype_val.comp (hα.comp continuous_fst)).sup
      (continuous_subtype_val.comp (hβ.comp continuous_snd))).subtype_mk _
  have hF10 : F (1, 0) = A := by
    apply Subtype.ext
    change (α 1).val ⊔ (β 0).val = A.val
    rw [hα1, hβ0, sup_eq_left]
    exact Set.singleton_subset_iff.mpr hxA
  have hF01 : F (0, 1) = B := by
    apply Subtype.ext
    change (α 0).val ⊔ (β 1).val = B.val
    rw [hα0, hβ1, sup_eq_right]
    exact Set.singleton_subset_iff.mpr hxB
  let f := σ ∘ F
  have hf : Continuous f := hσ.1.comp hF
  have hm : ∀ s, Monotone (fun u => f (s, u)) := by
    intro s u v huv
    exact hσ.2.2 _ _ (sup_le_sup_left (hmβ huv) _)
  have h0 : ∀ s, f (s, 0) ≤ t := by
    intro s
    rw [← hA.2]
    apply hσ.2.2
    change (α s).val ⊔ (β 0).val ≤ A.val
    rw [hβ0]
    exact sup_le (by simpa only [hα1] using hmα unitInterval.le_one')
      (Set.singleton_subset_iff.mpr hxA)
  have h1 : ∀ s, t ≤ f (s, 1) := by
    intro s
    rw [← hB.2]
    apply hσ.2.2
    change B.val ≤ (α s).val ⊔ (β 1).val
    rw [hβ1]
    exact le_sup_right
  let E := {p | f p = t}
  have hc : IsConnected E := connected_square_level f hf hm t h0 h1
  refine ⟨F '' E, ?_, ⟨(1, 0), ?_, hF10⟩, ⟨(0, 1), ?_, hF01⟩,
    hc.image F hF.continuousOn, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨?_, hp⟩
    have ha : (α p.1).val ≤ A.val := by
      simpa only [hα1] using hmα (show p.1 ≤ 1 from unitInterval.le_one')
    have hb : (β p.2).val ≤ B.val := by
      simpa only [hβ1] using hmβ (show p.2 ≤ 1 from unitInterval.le_one')
    exact sup_le (ha.trans hA.1) (hb.trans hB.1)
  · change σ (F (1, 0)) = t
    rw [hF10]
    exact hA.2
  · change σ (F (0, 1)) = t
    rw [hF01]
    exact hB.2
  · rintro _ ⟨p, _, rfl⟩
    exact Or.inl (hax p.1)

theorem isConnected_anchored_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y)
    {x : X} (hx : x ∈ (Y.val : Set X)) :
    IsConnected {K : Continuum X | K ∈ relativeLevel σ Y t ∧ x ∈ (K.val : Set X)} := by
  constructor
  · obtain ⟨K, hK, hxK⟩ := exists_mem_relativeLevel hσ Y ht htY hx
    exact ⟨K, hK, hxK⟩
  · apply isPreconnected_of_forall_pair
    intro A hA B hB
    obtain ⟨S, hS, hAS, hBS, hcS, hxS⟩ :=
      connected_relativeLevel_pair hσ Y A B t hA.1 hB.1 hA.2 hB.2
    exact ⟨S, fun K hK => ⟨hS hK, hxS K hK⟩, hAS, hBS, hcS.isPreconnected⟩

def familyUnion (S : Set (Continuum X)) : Set X :=
  ⋃ (K : Continuum X) (_hK : K ∈ S), (K.val : Set X)

omit [CompactSpace X] in
theorem isCompact_familyUnion {S : Set (Continuum X)} (hS : IsCompact S) :
    IsCompact (familyUnion S) := by
  have h := NonemptyCompacts.isCompact_biUnion_coe_of_isCompact
    (hS.image continuous_subtype_val)
  simpa only [familyUnion, biUnion_image] using h

omit [CompactSpace X] in
theorem isConnected_familyUnion {S : Set (Continuum X)} (hS : IsConnected S) :
    IsConnected (familyUnion S) := by
  let : TopologicalSpace (Set X) := .vietoris X
  obtain ⟨K, hK⟩ := hS.nonempty
  obtain ⟨x, hx⟩ := K.val.nonempty
  refine ⟨⟨x, mem_iUnion₂.mpr ⟨K, hK, hx⟩⟩, ?_⟩
  exact vietoris.isPreconnected_biUnion hS.isPreconnected
    (NonemptyCompacts.continuous_coe.comp continuous_subtype_val).continuousOn
    ⟨K, hK, K.property.isPreconnected⟩

theorem familyUnion_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y) :
    familyUnion (relativeLevel σ Y t) = (Y.val : Set X) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
    exact hK.1 hxK
  · intro x hx
    obtain ⟨K, hK, hxK⟩ := exists_mem_relativeLevel hσ Y ht htY hx
    exact mem_iUnion₂.mpr ⟨K, hK, hxK⟩

theorem isConnected_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y) :
    IsConnected (relativeLevel σ Y t) := by
  let L := relativeLevel σ Y t
  have hLc : IsCompact L := isCompact_relativeLevel hσ Y t
  constructor
  · obtain ⟨x, hx⟩ := Y.val.nonempty
    obtain ⟨K, hK, _⟩ := exists_mem_relativeLevel hσ Y ht htY hx
    exact ⟨K, hK⟩
  · apply isPreconnected_closed_iff.mpr
    intro P Q hP hQ hcover hLP hLQ
    let U := familyUnion (L ∩ P)
    let V := familyUnion (L ∩ Q)
    have hUc : IsCompact U := isCompact_familyUnion (hLc.inter_right hP)
    have hVc : IsCompact V := isCompact_familyUnion (hLc.inter_right hQ)
    have hYcover : (Y.val : Set X) ⊆ U ∪ V := by
      intro x hx
      obtain ⟨K, hK, hxK⟩ := exists_mem_relativeLevel hσ Y ht htY hx
      rcases hcover hK with hKP | hKQ
      · exact Or.inl (mem_iUnion₂.mpr ⟨K, ⟨hK, hKP⟩, hxK⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨K, ⟨hK, hKQ⟩, hxK⟩)
    have hYU : ((Y.val : Set X) ∩ U).Nonempty := by
      obtain ⟨K, hKL, hKP⟩ := hLP
      obtain ⟨x, hx⟩ := K.val.nonempty
      exact ⟨x, hKL.1 hx, mem_iUnion₂.mpr ⟨K, ⟨hKL, hKP⟩, hx⟩⟩
    have hYV : ((Y.val : Set X) ∩ V).Nonempty := by
      obtain ⟨K, hKL, hKQ⟩ := hLQ
      obtain ⟨x, hx⟩ := K.val.nonempty
      exact ⟨x, hKL.1 hx, mem_iUnion₂.mpr ⟨K, ⟨hKL, hKQ⟩, hx⟩⟩
    obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_closed_iff.mp Y.property.isPreconnected
      U V hUc.isClosed hVc.isClosed hYcover hYU hYV
    obtain ⟨A, ⟨hAL, hAP⟩, hxA⟩ := mem_iUnion₂.mp hxU
    obtain ⟨B, ⟨hBL, hBQ⟩, hxB⟩ := mem_iUnion₂.mp hxV
    obtain ⟨S, hS, hAS, hBS, hcS, _⟩ :=
      connected_relativeLevel_pair hσ Y A B t hAL hBL hxA hxB
    obtain ⟨K, hKS, hKP, hKQ⟩ := isPreconnected_closed_iff.mp hcS.isPreconnected
      P Q hP hQ (fun K hK => hcover (hS hK)) ⟨A, hAS, hAP⟩ ⟨B, hBS, hBQ⟩
    exact ⟨K, hS hKS, hKP, hKQ⟩

end WhitneyReversibility

#print axioms WhitneyReversibility.isConnected_relativeLevel
