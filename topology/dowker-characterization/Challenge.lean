/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.UnitInterval

/-!
# Dowker's countable paracompactness and insertion properties

The countable covering property below is stated using ordinary open-cover
refinements, independently of the characterization theorems.
AI implementation and review contributions are recorded in the project provenance.
-/

@[expose] public section

open Set

namespace Dowker

universe u

/-- Every countable family of open sets covering `X` has a locally finite open
refinement. The refinement may have any cardinality. -/
def CountablyParacompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), U.Countable → (∀ s ∈ U, IsOpen s) → ⋃₀ U = univ →
    ∃ V : Set (Set X), (∀ s ∈ V, IsOpen s) ∧ ⋃₀ V = univ ∧
      LocallyFinite (fun s : V => (s : Set X)) ∧ ∀ s ∈ V, ∃ t ∈ U, s ⊆ t

/-- Strict insertion for arbitrary real semicontinuous bounds, with no
boundedness or uniform-gap condition. -/
def StrictInsertion (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ h g : X → ℝ, UpperSemicontinuous h → LowerSemicontinuous g →
    (∀ x, h x < g x) → ∃ f : X → ℝ, Continuous f ∧ ∀ x, h x < f x ∧ f x < g x

end Dowker

/-!
# Countable open-cover refinements

The precise indexed refinement property is derived from the ordinary cover
definition; its index set is not imposed on the original refinement.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Regrouping a locally finite family by any map preserves local finiteness. -/
theorem locallyFinite_group {ι κ : Type*} {V : ι → Set X}
    (hV : LocallyFinite V) (a : ι → κ) :
    LocallyFinite (fun k => ⋃ i, ⋃ (_ : a i = k), V i) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := hV x
  refine ⟨t, ht, (hfin.image a).subset ?_⟩
  rintro k ⟨y, hy, hyt⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨hik, hyi⟩ := mem_iUnion.mp hi
  exact ⟨i, ⟨y, hyi, hyt⟩, hik⟩

/-- A countable indexed open cover admits a locally finite precise refinement. -/
theorem CountablyParacompact.precise_refinement (hX : CountablyParacompact X)
    {ι : Type*} [Countable ι] (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ ⋃ i, V i = univ ∧
      LocallyFinite V ∧ ∀ i, V i ⊆ U i := by
  classical
  obtain ⟨V, hVo, hVU, hVf, hVUsub⟩ := hX (range U) (countable_range U)
    (by rintro s ⟨i, rfl⟩; exact ho i) (by simpa only [sUnion_range] using hU)
  have ha : ∀ s : V, ∃ i, (s : Set X) ⊆ U i := by
    intro s
    obtain ⟨t, ⟨i, rfl⟩, hst⟩ := hVUsub s s.property
    exact ⟨i, hst⟩
  choose a ha using ha
  let W : ι → Set X := fun i => ⋃ s : V, ⋃ (_ : a s = i), (s : Set X)
  refine ⟨W, ?_, ?_, locallyFinite_group hVf a, ?_⟩
  · intro i
    exact isOpen_iUnion fun s => isOpen_iUnion fun _ => hVo s s.property
  · apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ V := hVU.symm ▸ mem_univ x
    obtain ⟨s, hsV, hxs⟩ := mem_sUnion.mp hx
    exact mem_iUnion.mpr ⟨a ⟨s, hsV⟩,
      mem_iUnion.mpr ⟨⟨s, hsV⟩, mem_iUnion.mpr ⟨rfl, hxs⟩⟩⟩
  · intro i x hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    obtain ⟨hsi, hxs⟩ := mem_iUnion.mp hs
    exact hsi ▸ ha s hxs

/-- The natural-number precise-refinement formulation is equivalent to the
ordinary countable-cover definition, including finite and empty covers. -/
theorem countablyParacompact_iff_nat_precise : CountablyParacompact X ↔
    ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → (⋃ n, U n = univ) →
      ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ ⋃ n, V n = univ ∧
        LocallyFinite V ∧ ∀ n, V n ⊆ U n := by
  constructor
  · intro h U ho hU
    exact h.precise_refinement U ho hU
  · intro h U hc ho hU
    by_cases hn : U.Nonempty
    · obtain ⟨u, rfl⟩ := hc.exists_eq_range hn
      obtain ⟨v, hvo, hvU, hvf, hvu⟩ := h u
        (fun n => ho _ (mem_range_self n)) (by simpa only [sUnion_range] using hU)
      refine ⟨range v, ?_, ?_, hvf.on_range, ?_⟩
      · rintro s ⟨n, rfl⟩; exact hvo n
      · simpa only [sUnion_range] using hvU
      · rintro s ⟨n, rfl⟩
        exact ⟨u n, mem_range_self n, hvu n⟩
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hn
      refine ⟨∅, by simp, ?_, ?_, by simp⟩
      · simpa [he] using hU
      · intro x
        refine ⟨univ, univ_mem, ?_⟩
        have hem : {i : (∅ : Set (Set X)) | ((i : Set X) ∩ univ).Nonempty} = ∅ := by
          ext i
          exact False.elim i.property
        rw [hem]
        exact finite_empty

end Dowker

/-!
# The decreasing closed sequence characterization

This is Dowker's Theorem 2(d), proved equivalent to the independent ordinary
cover definition in normal spaces.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Open expansions with empty intersection for decreasing closed sequences. -/
def ClosedSequenceProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ F : ℕ → Set X, (∀ n, IsClosed (F n)) → Antitone F → (⋂ n, F n) = ∅ →
    ∃ G : ℕ → Set X, (∀ n, IsOpen (G n)) ∧ (∀ n, F n ⊆ G n) ∧ (⋂ n, G n) = ∅

theorem CountablyParacompact.closed_sequence_property [NormalSpace X]
    (hX : CountablyParacompact X) : ClosedSequenceProperty X := by
  intro F hFc _ hFe
  have hcov : (⋃ n, (F n)ᶜ) = univ := by
    rw [← compl_iInter, hFe, compl_empty]
  obtain ⟨V, hVo, hVU, hVf, hVF⟩ :=
    hX.precise_refinement (fun n => (F n)ᶜ) (fun n => (hFc n).isOpen_compl) hcov
  obtain ⟨W, hWU, _, hWV⟩ :=
    exists_iUnion_eq_closure_subset hVo (hVf.point_finite) hVU
  refine ⟨fun n => (closure (W n))ᶜ, (fun _ => isClosed_closure.isOpen_compl), ?_, ?_⟩
  · intro n x hx hxc
    exact hVF n (hWV n hxc) hx
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxW : x ∈ ⋃ n, W n := hWU.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxW
    exact (mem_iInter.mp hx n) (subset_closure hn)

theorem countablyParacompact_of_closed_sequence_property [NormalSpace X]
    (hX : ClosedSequenceProperty X) : CountablyParacompact X := by
  apply countablyParacompact_iff_nat_precise.mpr
  intro U hUo hUU
  classical
  let F : ℕ → Set X := fun n => ⋂ k, ⋂ (_ : k ≤ n), (U k)ᶜ
  have hFc : ∀ n, IsClosed (F n) := fun n =>
    isClosed_iInter fun k => isClosed_iInter fun _ => (hUo k).isClosed_compl
  have hFa : Antitone F := by
    intro n m hnm x hx
    exact mem_iInter₂.mpr fun k hkn => mem_iInter₂.mp hx k (hkn.trans hnm)
  have hFe : (⋂ n, F n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxU : x ∈ ⋃ n, U n := hUU.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact mem_iInter₂.mp (mem_iInter.mp hx n) n le_rfl hn
  obtain ⟨G, hGo, hFG, hGe⟩ := hX F hFc hFa hFe
  choose O hOo hFO hOG using fun n => normal_exists_closure_subset (hFc n) (hGo n) (hFG n)
  let V : ℕ → Set X := fun n => U n ∩ ⋂ j : Fin n, O j
  refine ⟨V, (fun n => (hUo n).inter (isOpen_iInter_of_finite fun j => hOo j)), ?_, ?_,
    (fun _ => inter_subset_left)⟩
  · apply eq_univ_of_forall
    intro x
    have hxU : ∃ n, x ∈ U n := mem_iUnion.mp (hUU.symm ▸ mem_univ x)
    let m := Nat.find hxU
    refine mem_iUnion.mpr ⟨m, Nat.find_spec hxU, mem_iInter.mpr ?_⟩
    intro j
    apply hFO j
    refine mem_iInter₂.mpr fun k hkj => ?_
    exact Nat.find_min hxU (lt_of_le_of_lt hkj j.isLt)
  · intro x
    have hxG : ∃ n, x ∉ G n := by
      by_contra! hn
      have : x ∈ ⋂ n, G n := mem_iInter.mpr hn
      rw [hGe] at this
      exact this
    obtain ⟨n, hn⟩ := hxG
    have hxn : x ∈ (closure (O n))ᶜ := fun hx => hn (hOG n hx)
    refine ⟨(closure (O n))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxn,
      (finite_Iic n).subset ?_⟩
    intro m hm
    change m ≤ n
    by_contra! hnm
    obtain ⟨y, hyV, hyO⟩ := hm
    exact hyO (subset_closure (mem_iInter.mp hyV.2 ⟨n, hnm⟩))

theorem countablyParacompact_iff_closed_sequence_property [NormalSpace X] :
    CountablyParacompact X ↔ ClosedSequenceProperty X :=
  ⟨CountablyParacompact.closed_sequence_property,
    countablyParacompact_of_closed_sequence_property⟩

end Dowker

/-! # Positive reciprocal thresholds converging to zero -/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Dowker

def threshold (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem threshold_pos (n : ℕ) : 0 < threshold n := by
  unfold threshold
  positivity

theorem threshold_le_one (n : ℕ) : threshold n ≤ 1 := by
  unfold threshold
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  simp

theorem threshold_antitone : Antitone threshold := by
  intro n m hnm
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem exists_threshold_lt {a : ℝ} (ha : 0 < a) : ∃ n, threshold n < a := by
  exact exists_nat_one_div_lt ha

theorem threshold_tendsto : Tendsto threshold atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans (threshold_pos n)
  · intro a ha
    obtain ⟨n, hn⟩ := exists_threshold_lt ha
    exact eventually_atTop.mpr ⟨n, fun m hm => (threshold_antitone hm).trans_lt hn⟩

def intervalThreshold (n : ℕ) : unitInterval :=
  ⟨threshold n, (threshold_pos n).le, threshold_le_one n⟩

theorem intervalThreshold_ne_zero (n : ℕ) : intervalThreshold n ≠ 0 := by
  intro h
  have he := congrArg (fun t : unitInterval => (t : ℝ)) h
  exact (ne_of_gt (threshold_pos n)) he

theorem intervalThreshold_tendsto : Tendsto intervalThreshold atTop (𝓝 0) :=
  tendsto_subtype_rng.mpr threshold_tendsto

end Dowker

/-!
# Strict insertion from normality and countable paracompactness

A locally finite partition of unity subordinate to rational intermediate levels
gives a continuous weighted average between arbitrary semicontinuous bounds.
The sum is locally finite, so neither bound needs to be globally bounded.
-/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Normal countably paracompact spaces have strict insertion for all real
semicontinuous bounds. -/
theorem CountablyParacompact.strict_insertion [NormalSpace X]
    (hX : CountablyParacompact X) : StrictInsertion X := by
  classical
  intro h g hh hg hlt
  let U : ℚ → Set X := fun q => {x | h x < (q : ℝ) ∧ (q : ℝ) < g x}
  have ho : ∀ q, IsOpen (U q) := fun q =>
    (hh.isOpen_preimage (q : ℝ)).inter (hg.isOpen_preimage (q : ℝ))
  have hU : (⋃ q, U q) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨q, hq⟩ := exists_rat_btwn (hlt x)
    exact mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨V, hVo, hVU, hVf, hVUsub⟩ := hX.precise_refinement U ho hU
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ V hVo hVf (by rw [hVU])
  let f : X → ℝ := fun x => ∑ᶠ q : ℚ, ρ q x • (q : ℝ)
  refine ⟨f, ρ.continuous_finsum_smul (fun _ _ _ => continuousAt_const), ?_⟩
  intro x
  have hsum : ∑ q ∈ ρ.finsupport x, ρ q x = 1 := ρ.sum_finsupport (mem_univ x)
  have hf : f x = ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := by
    exact (ρ.sum_finsupport_smul_eq_finsum (fun q _ => (q : ℝ))).symm
  have hpos : ∀ q ∈ ρ.finsupport x, 0 < ρ q x := by
    intro q hq
    exact lt_of_le_of_ne (ρ.nonneg q x) (Ne.symm ((ρ.mem_finsupport x).mp hq))
  have hb : ∀ q ∈ ρ.finsupport x, h x < (q : ℝ) ∧ (q : ℝ) < g x := by
    intro q hq
    exact hVUsub q (hρ q (subset_closure ((ρ.mem_finsupport x).mp hq)))
  obtain ⟨q₀, hq₀⟩ := ρ.exists_pos (mem_univ x)
  have hq₀mem : q₀ ∈ ρ.finsupport x := (ρ.mem_finsupport x).mpr (ne_of_gt hq₀)
  constructor
  · calc
      h x = ∑ q ∈ ρ.finsupport x, ρ q x * h x := by rw [← Finset.sum_mul, hsum, one_mul]
      _ < ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := by
        apply Finset.sum_lt_sum
        · intro q hq
          exact (mul_lt_mul_of_pos_left (hb q hq).1 (hpos q hq)).le
        · exact ⟨q₀, hq₀mem, mul_lt_mul_of_pos_left (hb q₀ hq₀mem).1 hq₀⟩
      _ = f x := hf.symm
  · calc
      f x = ∑ q ∈ ρ.finsupport x, ρ q x * (q : ℝ) := hf
      _ < ∑ q ∈ ρ.finsupport x, ρ q x * g x := by
        apply Finset.sum_lt_sum
        · intro q hq
          exact (mul_lt_mul_of_pos_left (hb q hq).2 (hpos q hq)).le
        · exact ⟨q₀, hq₀mem, mul_lt_mul_of_pos_left (hb q₀ hq₀mem).2 hq₀⟩
      _ = g x := by rw [← Finset.sum_mul, hsum, one_mul]

end Dowker

/-!
# Normality and countable paracompactness from strict insertion

Closed-set indicators recover normality. The reciprocal of the first index
outside a decreasing closed sequence is positive and lower semicontinuous;
inserting a positive continuous minorant recovers the closed-sequence property.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

theorem StrictInsertion.normal_space (hI : StrictInsertion X) : NormalSpace X := by
  classical
  constructor
  intro A B hA hB hd
  let h : X → ℝ := A.indicator (fun _ => 1)
  let g : X → ℝ := fun x => 2 + B.indicator (fun _ => (-1 : ℝ)) x
  have hh : UpperSemicontinuous h := hA.upperSemicontinuous_indicator (by norm_num)
  have hg : LowerSemicontinuous g :=
    continuous_const.lowerSemicontinuous.add (hB.lowerSemicontinuous_indicator (by norm_num))
  have hlt : ∀ x, h x < g x := by
    intro x
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := fun hxB => Set.disjoint_left.mp hd hxA hxB
      norm_num [h, g, hxA, hxB]
    · by_cases hxB : x ∈ B <;> norm_num [h, g, hxA, hxB]
  obtain ⟨f, hf, hb⟩ := hI h g hh hg hlt
  refine ⟨{x | 1 < f x}, {x | f x < 1}, isOpen_lt continuous_const hf,
    isOpen_lt hf continuous_const, ?_, ?_, ?_⟩
  · intro x hx
    simpa [h, hx] using (hb x).1
  · intro x hx
    have hxg : g x = 1 := by norm_num [g, hx]
    change f x < 1
    rw [← hxg]
    exact (hb x).2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    change (1 : ℝ) < f x at hx
    change f x < 1 at hy
    exact (not_lt_of_gt hx) hy

theorem StrictInsertion.closed_sequence_property (hI : StrictInsertion X) :
    ClosedSequenceProperty X := by
  classical
  intro F hFc hFa hFe
  have he : ∀ x : X, ∃ n, x ∉ F n := by
    intro x
    by_contra! hx
    have hmem : x ∈ ⋂ n, F n := mem_iInter.mpr hx
    rw [hFe] at hmem
    exact hmem
  let escape : X → ℕ := fun x => Nat.find (he x)
  let g : X → ℝ := fun x => threshold (escape x)
  have hg : LowerSemicontinuous g := by
    intro x a ha
    have hx : x ∈ (F (escape x))ᶜ := Nat.find_spec (he x)
    filter_upwards [(hFc (escape x)).isOpen_compl.mem_nhds hx] with y hy
    have hyfind : escape y ≤ escape x := Nat.find_min' (he y) hy
    exact ha.trans_le (threshold_antitone hyfind)
  obtain ⟨f, hf, hfg⟩ := hI (fun _ => 0) g continuous_const.upperSemicontinuous hg
    (fun x => threshold_pos (escape x))
  refine ⟨fun n => {x | f x < threshold n},
    (fun _ => isOpen_lt hf continuous_const), ?_, ?_⟩
  · intro n x hx
    have hn : n ≤ escape x := by
      by_contra! hn
      exact Nat.find_spec (he x) (hFa hn.le hx)
    exact (hfg x).2.trans_le (threshold_antitone hn)
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_threshold_lt (hfg x).1
    exact hn.not_gt (mem_iInter.mp hx n)

theorem StrictInsertion.countably_paracompact (hI : StrictInsertion X) :
    CountablyParacompact X := by
  let := hI.normal_space
  exact countablyParacompact_of_closed_sequence_property hI.closed_sequence_property

end Dowker

/-!
# Normal products with compact metrizable spaces

Finite unions of members of a countable basis form countably many candidate
neighborhoods for compact fibers. Compactness makes the corresponding conditions
on the first coordinate open. A locally finite shrinking then separates the
two closed sets in the product. Only the compact factor needs regularity.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology

namespace Dowker

variable {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]

abbrev ProductCandidate (K : Type*) [TopologicalSpace K] [SecondCountableTopology K] :=
  Finset (countableBasis K)

def candidateOpen [SecondCountableTopology K] (s : ProductCandidate K) : Set K :=
  ⋃ i ∈ s, (i : Set K)

theorem candidateOpen_isOpen [SecondCountableTopology K] (s : ProductCandidate K) :
    IsOpen (candidateOpen s) :=
  isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_of_mem_countableBasis i.property

theorem exists_candidate [RegularSpace K] [SecondCountableTopology K]
    {A D : Set K} (hA : IsCompact A) (hD : IsClosed D) (hd : Disjoint A D) :
    ∃ s : ProductCandidate K, A ⊆ candidateOpen s ∧ closure (candidateOpen s) ⊆ Dᶜ := by
  classical
  let E : Set (countableBasis K) := {i | closure (i : Set K) ⊆ Dᶜ}
  have hcov : A ⊆ ⋃ i ∈ E, (i : Set K) := by
    intro y hy
    have hyD : y ∈ Dᶜ := fun hyD => Set.disjoint_left.mp hd hy hyD
    obtain ⟨i, hi, hyi, hiD⟩ :=
      (isBasis_countableBasis K).exists_closure_subset (hD.isOpen_compl.mem_nhds hyD)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, mem_iUnion.mpr ⟨hiD, hyi⟩⟩
  obtain ⟨E', hE', hEf, hAcov⟩ := hA.elim_finite_subcover_image
    (fun i _ => isOpen_of_mem_countableBasis i.property) hcov
  refine ⟨hEf.toFinset, ?_, ?_⟩
  · simpa only [candidateOpen, Set.Finite.mem_toFinset] using hAcov
  · intro y hy
    rw [candidateOpen, Finset.closure_biUnion] at hy
    obtain ⟨i, hi'⟩ := mem_iUnion.mp hy
    obtain ⟨hi, hyi⟩ := mem_iUnion.mp hi'
    have hiE : i ∈ E' := by simpa only [Set.Finite.mem_toFinset] using hi
    exact hE' hiE hyi

/-- A normal countably paracompact space has normal product with any compact,
regular, second-countable space. -/
theorem CountablyParacompact.normal_product [NormalSpace X] [CompactSpace K]
    [RegularSpace K] [SecondCountableTopology K] (hX : CountablyParacompact X) :
    NormalSpace (X × K) := by
  classical
  constructor
  intro A D hA hD hd
  let H : ProductCandidate K → Set K := candidateOpen
  let P : ProductCandidate K → Set X := fun s =>
    Prod.fst '' (A ∩ (univ ×ˢ (H s)ᶜ))
  let Q : ProductCandidate K → Set X := fun s =>
    Prod.fst '' (D ∩ (univ ×ˢ closure (H s)))
  let U : ProductCandidate K → Set X := fun s => (P s)ᶜ ∩ (Q s)ᶜ
  have hUo : ∀ s, IsOpen (U s) := by
    intro s
    exact (isClosedMap_fst_of_compactSpace _
      (hA.inter (isClosed_univ.prod (candidateOpen_isOpen s).isClosed_compl))).isOpen_compl.inter
      (isClosedMap_fst_of_compactSpace _
        (hD.inter (isClosed_univ.prod isClosed_closure))).isOpen_compl
  have hUc : (⋃ s, U s) = univ := by
    apply eq_univ_of_forall
    intro x
    have hc : Continuous (fun y : K => (x, y)) := continuous_const.prodMk continuous_id
    have hAx : IsCompact ((fun y => (x, y)) ⁻¹' A) := (hA.preimage hc).isCompact
    have hDx : IsClosed ((fun y => (x, y)) ⁻¹' D) := hD.preimage hc
    have hdx : Disjoint ((fun y => (x, y)) ⁻¹' A) ((fun y => (x, y)) ⁻¹' D) :=
      Set.disjoint_left.mpr fun y hyA hyD => Set.disjoint_left.mp hd hyA hyD
    obtain ⟨s, hsA, hsD⟩ := exists_candidate hAx hDx hdx
    refine mem_iUnion.mpr ⟨s, ?_, ?_⟩
    · rintro ⟨p, hp, hpx⟩
      exact hp.2.2 (hsA (by simpa [← hpx] using hp.1))
    · rintro ⟨p, hp, hpx⟩
      exact hsD hp.2.2 (by simpa [← hpx] using hp.1)
  obtain ⟨V, hVo, hVc, hVf, hVU⟩ := hX.precise_refinement U hUo hUc
  obtain ⟨W, hWc, hWo, hWV⟩ := exists_iUnion_eq_closure_subset hVo hVf.point_finite hVc
  have hWf : LocallyFinite W := hVf.subset fun s => subset_closure.trans (hWV s)
  let S : Set (X × K) := ⋃ s, W s ×ˢ H s
  have hSo : IsOpen S := isOpen_iUnion fun s => (hWo s).prod (candidateOpen_isOpen s)
  have hAS : A ⊆ S := by
    intro p hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hWc.symm ▸ mem_univ p.1)
    refine mem_iUnion.mpr ⟨s, hs, ?_⟩
    have hpU : p.1 ∈ U s := hVU s (hWV s (subset_closure hs))
    by_contra hpH
    exact hpU.1 ⟨p, ⟨hp, mem_univ p.1, hpH⟩, rfl⟩
  have hSD : Disjoint (closure S) D := by
    apply Set.disjoint_left.mpr
    intro p hp hpD
    rw [hWf.prod_right H |>.closure_iUnion] at hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    rw [closure_prod_eq] at hs
    have hpU : p.1 ∈ U s := hVU s (hWV s hs.1)
    exact hpU.2 ⟨p, ⟨hpD, mem_univ p.1, hs.2⟩, rfl⟩
  refine ⟨S, (closure S)ᶜ, hSo, isClosed_closure.isOpen_compl, hAS, ?_, ?_⟩
  · intro p hpD hpS
    exact Set.disjoint_left.mp hSD hpS hpD
  · exact Set.disjoint_left.mpr fun p hpS hpC => hpC (subset_closure hpS)

/-- Dowker's compact metrizable product theorem; no separation condition is
imposed on the first factor beyond normality. -/
theorem CountablyParacompact.normal_compact_metrizable_product [NormalSpace X]
    [CompactSpace K] [MetrizableSpace K] (hX : CountablyParacompact X) :
    NormalSpace (X × K) := hX.normal_product

end Dowker

/-!
# Countable paracompactness from normality of the interval product

A decreasing closed sequence with empty intersection is locally finite.
Placing its members at positive levels converging to zero therefore produces
a closed set disjoint from the zero slice. Normal separation gives the open
expansions required by the closed-sequence characterization.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem normal_space_of_normal_product [Nonempty Y] [NormalSpace (X × Y)] :
    NormalSpace X := by
  classical
  let y : Y := Classical.choice inferInstance
  have hc : Continuous (fun x : X => (x, y)) := continuous_id.prodMk continuous_const
  constructor
  intro A B hA hB hd
  have hdp : Disjoint (A ×ˢ (univ : Set Y)) (B ×ˢ (univ : Set Y)) :=
    Set.disjoint_left.mpr fun _ ha hb => Set.disjoint_left.mp hd ha.1 hb.1
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
    normal_separation (hA.prod isClosed_univ) (hB.prod isClosed_univ) hdp
  refine ⟨(fun x => (x, y)) ⁻¹' U, (fun x => (x, y)) ⁻¹' V,
    hUo.preimage hc, hVo.preimage hc, ?_, ?_, ?_⟩
  · intro x hx
    exact hAU ⟨hx, mem_univ y⟩
  · intro x hx
    exact hBV ⟨hx, mem_univ y⟩
  · exact Set.disjoint_left.mpr fun x hx hy => Set.disjoint_left.mp hUV hx hy

theorem locallyFinite_of_antitone_closed_empty_intersection
    (F : ℕ → Set X) (hFc : ∀ n, IsClosed (F n)) (hFa : Antitone F)
    (hFe : (⋂ n, F n) = ∅) : LocallyFinite F := by
  intro x
  have he : ∃ n, x ∉ F n := by
    by_contra! hx
    have hmem : x ∈ ⋂ n, F n := mem_iInter.mpr hx
    rw [hFe] at hmem
    exact hmem
  obtain ⟨n, hn⟩ := he
  refine ⟨(F n)ᶜ, (hFc n).isOpen_compl.mem_nhds hn, (finite_Iio n).subset ?_⟩
  intro m hm
  by_contra! hnm
  obtain ⟨y, hyF, hyc⟩ := hm
  exact hyc (hFa (le_of_not_gt hnm) hyF)

theorem closed_sequence_property_of_normal_interval_product
    [NormalSpace (X × unitInterval)] : ClosedSequenceProperty X := by
  intro F hFc hFa hFe
  let A : Set (X × unitInterval) := ⋃ n, F n ×ˢ {intervalThreshold n}
  let B : Set (X × unitInterval) := univ ×ˢ {0}
  have hLF := locallyFinite_of_antitone_closed_empty_intersection F hFc hFa hFe
  have hA : IsClosed A := (hLF.prod_right (fun n => {intervalThreshold n})).isClosed_iUnion
    (fun n => (hFc n).prod isClosed_singleton)
  have hB : IsClosed B := isClosed_univ.prod isClosed_singleton
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    obtain ⟨n, hn⟩ := mem_iUnion.mp hpA
    exact intervalThreshold_ne_zero n (hn.2.symm.trans hpB.2)
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ := normal_separation hA hB hd
  refine ⟨fun n => {x | (x, intervalThreshold n) ∈ U},
    (fun n => hUo.preimage (continuous_id.prodMk continuous_const)), ?_, ?_⟩
  · intro n x hx
    exact hAU (mem_iUnion.mpr ⟨n, hx, rfl⟩)
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxV : (x, (0 : unitInterval)) ∈ V := hBV ⟨mem_univ x, rfl⟩
    have ht : Tendsto (fun n => (x, intervalThreshold n)) atTop (𝓝 (x, (0 : unitInterval))) :=
      tendsto_const_nhds.prodMk_nhds intervalThreshold_tendsto
    obtain ⟨n, hn⟩ := (ht.eventually (hVo.mem_nhds hxV)).exists
    exact Set.disjoint_left.mp hUV (mem_iInter.mp hx n) hn

theorem countably_paracompact_of_normal_interval_product
    [NormalSpace (X × unitInterval)] : CountablyParacompact X := by
  let : NormalSpace X := normal_space_of_normal_product (Y := unitInterval)
  exact countablyParacompact_of_closed_sequence_property
    closed_sequence_property_of_normal_interval_product

end Dowker

/-!
# Dowker's characterization

Normality together with ordinary countable paracompactness is equivalent both
to normality of the unit-interval product and to strict continuous insertion
between arbitrary real upper and lower semicontinuous bounds. The first factor
has no additional separation assumption. The companion theorem covers every compact
metrizable second factor.
-/

@[expose] public section

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

theorem normal_countablyParacompact_iff_normal_interval_product :
    (NormalSpace X ∧ CountablyParacompact X) ↔ NormalSpace (X × unitInterval) := by
  constructor
  · rintro ⟨hN, hC⟩
    let := hN
    exact hC.normal_compact_metrizable_product
  · intro hP
    let := hP
    exact ⟨normal_space_of_normal_product (Y := unitInterval),
      countably_paracompact_of_normal_interval_product⟩

theorem normal_countablyParacompact_iff_strict_insertion :
    (NormalSpace X ∧ CountablyParacompact X) ↔ StrictInsertion X := by
  constructor
  · rintro ⟨hN, hC⟩
    let := hN
    exact hC.strict_insertion
  · intro hI
    exact ⟨hI.normal_space, hI.countably_paracompact⟩

theorem normal_interval_product_iff_strict_insertion :
    NormalSpace (X × unitInterval) ↔ StrictInsertion X :=
  normal_countablyParacompact_iff_normal_interval_product.symm.trans
    normal_countablyParacompact_iff_strict_insertion

end Dowker
