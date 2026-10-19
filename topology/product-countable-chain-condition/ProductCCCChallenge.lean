/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Material Lean proof authorship: OpenAI Codex. Classical source: Nina M. Roy,
Is the product of ccc spaces a ccc space?, pp.174–176, Theorem 2.2 and Corollary 2.3.
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Data.Set.Pairwise.Chain
public import Mathlib.Order.Zorn
public import Mathlib.Data.Finset.Card

public section

open Set Function Topology TopologicalSpace

namespace ProductCCC

/-- Every set-family of pairwise disjoint nonempty open sets is countable. -/
@[expose] def HasCCC (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (A : Set (Set X)), (∀ U ∈ A, IsOpen U ∧ U.Nonempty) →
    A.Pairwise Disjoint → A.Countable

/-- An indexed finite-set family has fixed pairwise intersections on `J`. -/
@[expose] def IsDeltaSystem {ι α : Type*} (s : ι → Finset α) (J : Set ι) (root : Finset α) : Prop := by
  classical
  exact ∀ i ∈ J, ∀ j ∈ J, i ≠ j → s i ∩ s j = root

private theorem exists_maximal_disjoint {ι α : Type*} (s : ι → Finset α) (I : Set ι) :
    ∃ M ⊆ I, M.Pairwise (fun i j => Disjoint (s i) (s j)) ∧
      ∀ j ∈ I, j ∉ M → ∃ i ∈ M, ¬ Disjoint (s j) (s i) := by
  classical
  let S : Set (Set ι) := {J | J ⊆ I ∧ J.Pairwise (fun i j => Disjoint (s i) (s j))}
  obtain ⟨M, hM, hmax⟩ := zorn_subset S (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun J hJ => subset_sUnion_of_mem hJ⟩
    refine ⟨sUnion_subset fun J hJ => (hc hJ).1, ?_⟩
    exact hchain.pairwise_sUnion.mpr (fun J hJ => (hc hJ).2))
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro j hj hjM
  by_contra! h
  have he : insert j M ∈ S := ⟨insert_subset hj hM.1,
    hM.2.insert (fun i hi _ => ⟨h i hi, (h i hi).symm⟩)⟩
  exact hjM (hmax he (subset_insert j M) (mem_insert j M))

private theorem disjoint_uncountable {ι α : Type*} (s : ι → Finset α) (I : Set ι)
    (hI : ¬ I.Countable) (hf : ∀ a, {i ∈ I | a ∈ s i}.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ IsDeltaSystem s J ∅ := by
  classical
  obtain ⟨M, hMI, hM, hm⟩ := exists_maximal_disjoint s I
  refine ⟨M, hMI, ?_, ?_⟩
  · intro hMc
    have hU : (⋃ i ∈ M, (s i : Set α)).Countable :=
      hMc.biUnion (fun i _ => (s i).countable_toSet)
    have hC := hU.biUnion (fun a _ => hf a)
    apply hI
    apply (hMc.union hC).mono
    intro j hj
    by_cases hjM : j ∈ M
    · exact Or.inl hjM
    · obtain ⟨i, hi, hji⟩ := hm j hj hjM
      obtain ⟨a, haj, hai⟩ := Finset.not_disjoint_iff.mp hji
      exact Or.inr (mem_iUnion₂.mpr ⟨a, mem_iUnion₂.mpr ⟨i, hi, hai⟩, hj, haj⟩)
  · intro i hi j hj hij
    exact Finset.disjoint_iff_inter_eq_empty.mp (hM hi hj hij)

private theorem delta_bounded (n : ℕ) {ι α : Type*} (s : ι → Finset α) (I : Set ι)
    (hI : ¬ I.Countable) (hsize : ∀ i ∈ I, (s i).card ≤ n) :
    ∃ J ⊆ I, ¬ J.Countable ∧ ∃ root, IsDeltaSystem s J root := by
  classical
  induction n generalizing ι I with
  | zero =>
    refine ⟨I, subset_rfl, hI, ∅, ?_⟩
    intro i hi j hj hij
    have hz : s i = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hsize i hi))
    simp [hz]
  | succ n ih =>
    by_cases h : ∃ a, ¬ {i ∈ I | a ∈ s i}.Countable
    · obtain ⟨a, ha⟩ := h
      obtain ⟨J, hJI, hJ, root, hroot⟩ := ih (fun i => (s i).erase a)
        {i ∈ I | a ∈ s i} ha (by
          intro i hi
          rw [Finset.card_erase_of_mem hi.2]
          have := hsize i hi.1
          have := Finset.card_pos.mpr ⟨a, hi.2⟩
          omega)
      refine ⟨J, fun i hi => (hJI hi).1, hJ, insert a root, ?_⟩
      intro i hi j hj hij
      have hr := hroot i hi j hj hij
      ext x
      by_cases hx : x = a
      · subst x
        simp [(hJI hi).2, (hJI hj).2]
      · have hh := Finset.ext_iff.mp hr x
        simpa [hx] using hh
    · obtain ⟨J, hJI, hJ, hroot⟩ := disjoint_uncountable s I (hI) (by simpa using h)
      exact ⟨J, hJI, hJ, ∅, hroot⟩

/-- The uncountable delta-system lemma, indexed form; repeated finite supports are allowed. -/
theorem uncountable_delta_system {ι α : Type*} (s : ι → Finset α) (I : Set ι)
    (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ ∃ root, IsDeltaSystem s J root := by
  classical
  have hn : ∃ n, ¬ {i ∈ I | (s i).card = n}.Countable := by
    by_contra! h
    apply hI
    apply (countable_iUnion h).mono
    intro i hi
    exact mem_iUnion.mpr ⟨(s i).card, hi, rfl⟩
  obtain ⟨n, hn⟩ := hn
  obtain ⟨J, hJI, hJ, r, hr⟩ := delta_bounded n s {i ∈ I | (s i).card = n} hn
    (fun i hi => hi.2.le)
  exact ⟨J, fun i hi => (hJI hi).1, hJ, r, hr⟩

/-- Indexed form of the cellularity condition, with an index universe independent of `X`. -/
theorem HasCCC.countable_index {X : Type*} [TopologicalSpace X] (h : HasCCC X)
    {ι : Type*} (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hd : Pairwise (Disjoint on U)) : Countable ι := by
  classical
  have hc := h (range U) (by rintro _ ⟨i, rfl⟩; exact ⟨ho i, hne i⟩)
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      exact hd (fun he => hij (congrArg U he)))
  have hinj : Injective U := by
    intro i j hij
    by_contra hneij
    obtain ⟨x, hx⟩ := hne i
    exact Set.disjoint_left.mp (hd hneij) hx (hij ▸ hx)
  exact (Set.countable_univ_iff.mp
    (countable_of_injective_of_countable_image hinj.injOn (by simpa using hc)))

/-- Separability implies CCC, using Mathlib's disjoint-open-family theorem. -/
theorem hasCCC_of_separable (X : Type*) [TopologicalSpace X] [SeparableSpace X] :
    HasCCC X := by
  intro A hA hd
  have : Countable A := (hd.subtype _ _).countable_of_isOpen_disjoint
    (fun U => (hA U U.2).1) (fun U => (hA U U.2).2)
  exact this

/-- Roy's finite-subproduct theorem (Theorem 2.2). No nonemptiness or separation
assumption, index-cardinality bound, MA or CH is used. -/
theorem hasCCC_pi_of_finite {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)]
    (hfinite : ∀ s : Finset ι, HasCCC (∀ i : s, X i)) : HasCCC (∀ i, X i) := by
  classical
  intro A hA hd
  by_contra hAc
  have hdata : ∀ U : A, ∃ (x : ∀ i, X i) (s : Finset ι) (V : ∀ i, Set (X i)),
      (∀ i ∈ s, IsOpen (V i) ∧ x i ∈ V i) ∧ (s : Set ι).pi V ⊆ U := by
    intro U
    obtain ⟨x, hx⟩ := (hA U U.2).2
    obtain ⟨s, V, hV, hs⟩ := isOpen_pi_iff.mp (hA U U.2).1 x hx
    exact ⟨x, s, V, hV, hs⟩
  choose x s V hV hs using hdata
  obtain ⟨J, _, hJ, root, hroot⟩ := uncountable_delta_system s univ
    (by simpa only [countable_univ_iff, countable_coe_iff] using hAc)
  let W : J → Set (∀ i : root, X i) := fun j => univ.pi (fun i => V j.1 i)
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    isOpen_set_pi finite_univ (fun i _ => (hV j.1 i (by
      obtain ⟨k, hk, hkj⟩ := (show J.Infinite from fun h => hJ h.countable).exists_notMem_finset {j.1}
      have hi : i.1 ∈ s j.1 ∩ s k := by rw [hroot j.1 j.2 k hk (Ne.symm (by simpa using hkj))]
                                                        ; exact i.2
      exact (Finset.mem_inter.mp hi).1)).1)
  have hWne : ∀ j, (W j).Nonempty := by
    intro j
    refine ⟨fun i => x j.1 i, ?_⟩
    intro i _
    obtain ⟨k, hk, hkj⟩ := (show J.Infinite from fun h => hJ h.countable).exists_notMem_finset {j.1}
    have hi : i.1 ∈ s j.1 ∩ s k := by
      rw [hroot j.1 j.2 k hk (Ne.symm (by simpa using hkj))]
      exact i.2
    exact (hV j.1 i (Finset.mem_inter.mp hi).1).2
  have hWd : Pairwise (Disjoint on W) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro w hwj hwk
    have hjk' : j.1 ≠ k.1 := fun he => hjk (Subtype.ext he)
    have hr := hroot j.1 j.2 k.1 k.2 hjk'
    let z : ∀ i, X i := fun i => if hi : i ∈ root then w ⟨i, hi⟩
      else if i ∈ s j.1 then x j.1 i else x k.1 i
    have hzj : z ∈ (j.1 : Set (∀ i, X i)) := hs j.1 (by
      intro i hi
      change (if h : i ∈ root then w ⟨i, h⟩
        else if i ∈ s j.1 then x j.1 i else x k.1 i) ∈ V j.1 i
      split_ifs with hir hij
      · exact hwj ⟨i, hir⟩ (mem_univ _)
      · exact (hV j.1 i hi).2
      · exact False.elim (hij hi))
    have hzk : z ∈ (k.1 : Set (∀ i, X i)) := hs k.1 (by
      intro i hi
      change (if h : i ∈ root then w ⟨i, h⟩
        else if i ∈ s j.1 then x j.1 i else x k.1 i) ∈ V k.1 i
      split_ifs with hir hij
      · exact hwk ⟨i, hir⟩ (mem_univ _)
      · exact False.elim (hir (by rw [← hr]; exact Finset.mem_inter.mpr ⟨hij, hi⟩))
      · exact (hV k.1 i hi).2)
    exact Set.disjoint_left.mp (hd j.1.2 k.1.2
      (fun he => hjk' (Subtype.ext he))) hzj hzk
  have := (hfinite root).countable_index W hWo hWne hWd
  exact hJ this

/-- CCC is preserved by a continuous surjection. -/
theorem HasCCC.of_continuous_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : HasCCC X)
    {f : X → Y} (hf : Continuous f) (hsur : Surjective f) : HasCCC Y := by
  intro A hA hd
  apply countable_of_injective_of_countable_image hsur.preimage_injective.injOn
  apply h
  · rintro _ ⟨U, hU, rfl⟩
    refine ⟨(hA U hU).1.preimage hf, ?_⟩
    obtain ⟨y, hy⟩ := (hA U hU).2
    obtain ⟨x, rfl⟩ := hsur y
    exact ⟨x, hy⟩
  · rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩ hne
    exact (hd hU hV (fun he => hne (congrArg (Set.preimage f) he))).preimage f

/-- Nonempty factors make the finite projections surjective. The empty-index
product is permitted, and no separation hypothesis is needed. -/
theorem hasCCC_pi_iff {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, Nonempty (X i)] :
    HasCCC (∀ i, X i) ↔ ∀ s : Finset ι, HasCCC (∀ i : s, X i) := by
  classical
  constructor
  · intro h s
    apply h.of_continuous_surjective s.continuous_restrict
    intro y
    refine ⟨fun i => if hi : i ∈ s then y ⟨i, hi⟩ else Classical.choice (inferInstance), ?_⟩
    funext i
    simp only [Finset.restrict, dite_eq_left i.2]
  · exact hasCCC_pi_of_finite

/-- Roy's Corollary 2.3: arbitrary products of separable spaces are CCC.
Empty factors are allowed; no bound on the index cardinality is imposed. -/
theorem hasCCC_pi_of_separable {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, SeparableSpace (X i)] :
    HasCCC (∀ i, X i) := by
  apply hasCCC_pi_of_finite
  intro s
  exact hasCCC_of_separable _

/-- The discrete boundary: CCC is equivalent to countability. -/
theorem hasCCC_discrete_iff (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    HasCCC X ↔ Countable X := by
  constructor
  · intro h
    apply h.countable_index (fun x => {x}) (fun _ => isOpen_discrete _)
      (fun x => singleton_nonempty x)
    intro x y hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro h
    have := h
    exact hasCCC_of_separable X

end ProductCCC
