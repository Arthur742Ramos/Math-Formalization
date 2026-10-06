/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.GDelta.Basic

/-!
Indecomposability of compact Hausdorff continua, following Paul Bankston,
Metric Topology: A First Course, Propositions 29.1 and 29.2 and Exercise 29(6).
The continuum itself is the ambient type; interior therefore means relative interior.
-/

@[expose] public section

open Set
universe u
namespace IndecomposableContinuum
variable {X : Type u} [tX : TopologicalSpace X]

/-- A subcontinuum is a nonempty compact connected subset. -/
def IsSubcontinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K

/-- A space is indecomposable when no two proper subcontinua cover it.
The principal theorems assume separately that the space is a continuum. -/
def IsIndecomposable (X : Type u) [tX : TopologicalSpace X] : Prop :=
  ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L →
    K ∪ L = univ → K = univ ∨ L = univ

omit [TopologicalSpace X] in
private theorem side_eq_compl {A U V : Set X}
    (hcover : U ∪ V = Aᶜ) (hd : Disjoint U V) : A ∪ U = Vᶜ := by
  ext x
  have hc := congrArg (fun s : Set X => x ∈ s) hcover
  simp only [mem_union, mem_compl_iff] at hc ⊢
  have huv := disjoint_left.1 hd
  constructor
  · rintro (ha | hu) hv
    · exact (hc.mp (Or.inr hv)) ha
    · exact huv hu hv
  · intro hv
    by_cases ha : x ∈ A
    · exact Or.inl ha
    · exact Or.inr ((hc.mpr ha).resolve_right hv)

/-- Joining a connected closed set to either open side of its complement
gives a connected set. The side need not itself be connected. -/
private theorem connected_union_side [PreconnectedSpace X] {A U V : Set X}
    (hA : IsClosed A) (hAc : IsConnected A) (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hcover : U ∪ V = Aᶜ) : IsConnected (A ∪ U) := by
  refine ⟨hAc.nonempty.mono subset_union_left, ?_⟩
  have hclosed : IsClosed (A ∪ U) := by
    rw [side_eq_compl hcover hd]
    exact hV.isClosed_compl
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hclosed).2
  intro a b ha hb hc hab
  have hcase : ∀ a b : Set X, IsClosed a → IsClosed b →
      A ∪ U ⊆ a ∪ b → Disjoint a b → A ⊆ a → A ∪ U ⊆ a := by
    intro a b ha hb hc hd hAa
    have hAb : ∀ x ∈ A, x ∉ b := fun x hx hxb => disjoint_left.1 hd (hAa hx) hxb
    have heq : (A ∪ U) ∩ b = U ∩ aᶜ := by
      ext x
      constructor
      · rintro ⟨hx, hxb⟩
        exact ⟨hx.resolve_left (fun hxA => hAb x hxA hxb),
          fun hxa => disjoint_left.1 hd hxa hxb⟩
      · rintro ⟨hxU, hxa⟩
        exact ⟨Or.inr hxU, (hc (Or.inr hxU)).resolve_left hxa⟩
    have hclopen : IsClopen ((A ∪ U) ∩ b) :=
      ⟨hclosed.inter hb, heq ▸ hU.inter ha.isOpen_compl⟩
    have hempty : (A ∪ U) ∩ b = ∅ := by
      rcases isClopen_iff.mp hclopen with he | he
      · exact he
      · obtain ⟨x, hx⟩ := hAc.nonempty
        have hxB : x ∈ (A ∪ U) ∩ b := he ▸ mem_univ x
        exact (hAb x hx hxB.2).elim
    intro x hx
    exact (hc hx).resolve_right (fun hxb => by
      have : x ∈ (A ∪ U) ∩ b := ⟨hx, hxb⟩
      simp [hempty] at this)
  have hAcov : A ⊆ a ∪ b := subset_union_left.trans hc
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hA).1
      hAc.isPreconnected a b ha hb hAcov hab with h | h
  · exact Or.inl (hcase a b ha hb hc hab h)
  · exact Or.inr (hcase b a hb ha (by simpa [union_comm] using hc) hab.symm h)

private theorem exists_separation {A : Set X} (hA : IsClosed A)
    (hdis : ¬ IsPreconnected Aᶜ) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ U ∪ V = Aᶜ := by
  classical
  simp only [IsPreconnected, not_forall] at hdis
  obtain ⟨a, b, ha, hb, hc, hna, hnb, hd⟩ := hdis
  refine ⟨Aᶜ ∩ a, Aᶜ ∩ b, hA.isOpen_compl.inter ha,
    hA.isOpen_compl.inter hb, hna, hnb, ?_, ?_⟩
  · apply disjoint_left.2
    rintro x ⟨hx, hxa⟩ ⟨_, hxb⟩
    exact hd ⟨x, hx, hxa, hxb⟩
  · ext x
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases hc hx with hxa | hxb
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, hxb⟩

private theorem decomposable_of_disconnected_compl [cX : CompactSpace X]
    [PreconnectedSpace X] {K : Set X} (hK : IsClosed K) (hKc : IsConnected K)
    (hdis : ¬ IsPreconnected Kᶜ) :
    ∃ A B : Set X, IsSubcontinuum A ∧ IsSubcontinuum B ∧
      A ≠ univ ∧ B ≠ univ ∧ A ∪ B = univ := by
  obtain ⟨U, V, hU, hV, hnU, hnV, hd, hc⟩ := exists_separation hK hdis
  have hKU : K ∪ U = Vᶜ := side_eq_compl hc hd
  have hKV : K ∪ V = Uᶜ := side_eq_compl (by simpa [union_comm] using hc) hd.symm
  refine ⟨K ∪ U, K ∪ V, ⟨?_, connected_union_side hK hKc hU hV hd hc⟩,
    ⟨?_, connected_union_side hK hKc hV hU hd.symm (by simpa [union_comm] using hc)⟩,
    ?_, ?_, ?_⟩
  · rw [hKU]; exact hV.isClosed_compl.isCompact
  · rw [hKV]; exact hU.isClosed_compl.isCompact
  · obtain ⟨x, hx⟩ := hnV
    intro he
    have : x ∈ K ∪ U := he ▸ mem_univ x
    exact (hKU ▸ this) hx
  · obtain ⟨x, hx⟩ := hnU
    intro he
    have : x ∈ K ∪ V := he ▸ mem_univ x
    exact (hKV ▸ this) hx
  · calc
      (K ∪ U) ∪ (K ∪ V) = K ∪ (U ∪ V) := by ext x; simp only [mem_union]; tauto
      _ = univ := by rw [hc, union_compl_self]

omit [TopologicalSpace X] in
private theorem proper_compl_nonempty {K : Set X} (hK : K ≠ univ) : Kᶜ.Nonempty := by
  by_contra h
  apply hK
  have he := congrArg (fun s : Set X => sᶜ) (not_nonempty_iff_eq_empty.mp h)
  simpa using he

/-- A compact connected Hausdorff space is indecomposable exactly when
every proper subcontinuum has empty interior in that space. -/
theorem indecomposable_iff_empty_interior [cX : CompactSpace X] [hX : T2Space X]
    [cnX : ConnectedSpace X] :
    IsIndecomposable X ↔ ∀ K : Set X, IsSubcontinuum K → K ≠ univ → interior K = ∅ := by
  classical
  constructor
  · intro hi K hK hp
    by_contra hInt
    by_cases hpc : IsPreconnected Kᶜ
    · have hcc : IsConnected Kᶜ := ⟨proper_compl_nonempty hp, hpc⟩
      have hM : IsSubcontinuum (closure Kᶜ) := ⟨isClosed_closure.isCompact, hcc.closure⟩
      have hMp : closure Kᶜ ≠ univ := by
        rw [closure_compl]
        intro he
        have he' := congrArg (fun s : Set X => sᶜ) he
        exact hInt (by simpa using he')
      have hcover : K ∪ closure Kᶜ = univ := by
        apply subset_antisymm (subset_univ _)
        intro x _
        by_cases hx : x ∈ K
        · exact Or.inl hx
        · exact Or.inr (subset_closure hx)
      exact (hi K (closure Kᶜ) hK hM hcover).elim hp hMp
    · obtain ⟨A, B, hA, hB, hAp, hBp, hc⟩ :=
        decomposable_of_disconnected_compl hK.1.isClosed hK.2 hpc
      exact (hi A B hA hB hc).elim hAp hBp
  · intro h K L hK hL hc
    by_cases hKu : K = univ
    · exact Or.inl hKu
    · right
      by_contra hLu
      have hsub : Lᶜ ⊆ K := by
        intro x hx
        have hmem : x ∈ K ∪ L := hc ▸ mem_univ x
        exact hmem.resolve_right hx
      have hint : Lᶜ ⊆ interior K := interior_maximal hsub hL.1.isClosed.isOpen_compl
      obtain ⟨x, hx⟩ := proper_compl_nonempty hLu
      have : x ∈ interior K := hint hx
      rw [h K hK hKu] at this
      exact this

/-- The same characterization using Mathlib's nowhere-dense predicate. -/
theorem indecomposable_iff_nowhere_dense [cX : CompactSpace X] [hX : T2Space X]
    [cnX : ConnectedSpace X] :
    IsIndecomposable X ↔ ∀ K : Set X, IsSubcontinuum K → K ≠ univ → IsNowhereDense K := by
  rw [indecomposable_iff_empty_interior]
  constructor <;> intro h K hK hp
  · exact hK.1.isClosed.isNowhereDense_iff.mpr (h K hK hp)
  · exact hK.1.isClosed.isNowhereDense_iff.mp (h K hK hp)

/-- Removing a proper subcontinuum from an indecomposable continuum
leaves a nonempty connected set. -/
theorem connected_compl_of_proper_subcontinuum [cX : CompactSpace X] [hX : T2Space X]
    [cnX : ConnectedSpace X] (hi : IsIndecomposable X) {K : Set X}
    (hK : IsSubcontinuum K) (hp : K ≠ univ) : IsConnected Kᶜ := by
  refine ⟨proper_compl_nonempty hp, ?_⟩
  by_contra h
  obtain ⟨A, B, hA, hB, hAp, hBp, hc⟩ :=
    decomposable_of_disconnected_compl hK.1.isClosed hK.2 h
  exact (hi A B hA hB hc).elim hAp hBp

/-- Every point has preconnected complement. This includes a singleton continuum,
where the complement is empty. -/
theorem preconnected_compl_singleton [cX : CompactSpace X] [hX : T2Space X]
    [cnX : ConnectedSpace X] (hi : IsIndecomposable X) (x : X) : IsPreconnected ({x}ᶜ : Set X) := by
  by_cases hp : ({x} : Set X) = univ
  · rw [hp, compl_univ]; exact isPreconnected_empty
  · exact (connected_compl_of_proper_subcontinuum hi
      ⟨isCompact_singleton, isConnected_singleton⟩ hp).isPreconnected

/-- A nontrivial indecomposable continuum has no cut points, with nonempty
connected complements. -/
theorem connected_compl_singleton [cX : CompactSpace X] [hX : T2Space X]
    [cnX : ConnectedSpace X] [ntX : Nontrivial X] (hi : IsIndecomposable X) (x : X) :
    IsConnected ({x}ᶜ : Set X) := by
  refine ⟨?_, preconnected_compl_singleton hi x⟩
  obtain ⟨y, hy⟩ := exists_ne x
  exact ⟨y, by simpa using hy⟩

end IndecomposableContinuum

