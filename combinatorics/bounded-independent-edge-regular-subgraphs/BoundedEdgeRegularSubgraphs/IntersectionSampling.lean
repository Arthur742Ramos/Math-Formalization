module

public import BoundedEdgeRegularSubgraphs.IntersectionProbability
import Mathlib.Tactic

/-!
# Uniform intersections at a fixed overlap size
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Among fixed-order sets having a prescribed intersection size,
each possible intersection occurs the same number of times. -/
theorem sum_sample_intersection_of_card {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s S : Finset α) (hS : S ⊆ s) {k j : ℕ} (hj : j ≤ k) (g : Finset α → M) :
    (∑ T ∈ (s.powersetCard k).filter (fun T ↦ (S ∩ T).card = j), g (S ∩ T)) =
      ((s \ S).card.choose (k - j)) • ∑ J ∈ S.powersetCard j, g J := by
  classical
  let P := S.powersetCard j
  let Q := (s \ S).powersetCard (k - j)
  let V := (s.powersetCard k).filter (fun T ↦ (S ∩ T).card = j)
  have hleft {J U : Finset α} (hJ : J ∈ P) (hU : U ∈ Q) : S ∩ (J ∪ U) = J := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    have h₁ : x ∈ J → x ∈ S := fun h ↦ (Finset.mem_powersetCard.mp hJ).1 h
    have h₂ : x ∈ U → x ∉ S := fun h ↦ (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hU).1 h)).2
    tauto
  have hright {J U : Finset α} (hJ : J ∈ P) (hU : U ∈ Q) : (J ∪ U) \ S = U := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h₁ : x ∈ J → x ∈ S := fun h ↦ (Finset.mem_powersetCard.mp hJ).1 h
    have h₂ : x ∈ U → x ∉ S := fun h ↦ (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hU).1 h)).2
    tauto
  have hsum : (∑ C ∈ P ×ˢ Q, g C.1) = ∑ T ∈ V, g (S ∩ T) := by
    refine Finset.sum_bij (fun C _ ↦ C.1 ∪ C.2) ?_ ?_ ?_ ?_
    · intro C hC
      obtain ⟨hJ, hU⟩ := Finset.mem_product.mp hC
      obtain ⟨hJ₁, hJ₂⟩ := Finset.mem_powersetCard.mp hJ
      obtain ⟨hU₁, hU₂⟩ := Finset.mem_powersetCard.mp hU
      have hd : Disjoint C.1 C.2 := by
        rw [Finset.disjoint_left]
        exact fun x hx hu ↦ (Finset.mem_sdiff.mp (hU₁ hu)).2 (hJ₁ hx)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.union_subset (hJ₁.trans hS)
        (hU₁.trans Finset.sdiff_subset), ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hd, hJ₂, hU₂]
        omega
      · rw [hleft hJ hU, hJ₂]
    · intro A hA B hB h
      obtain ⟨hA₁, hA₂⟩ := Finset.mem_product.mp hA
      obtain ⟨hB₁, hB₂⟩ := Finset.mem_product.mp hB
      apply Prod.ext
      · simpa only [hleft hA₁ hA₂, hleft hB₁ hB₂] using congrArg (fun T ↦ S ∩ T) h
      · simpa only [hright hA₁ hA₂, hright hB₁ hB₂] using congrArg (fun T ↦ T \ S) h
    · intro T hT
      obtain ⟨hT₀, hJ⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTs, hTk⟩ := Finset.mem_powersetCard.mp hT₀
      have hCard : (T \ S).card + (S ∩ T).card = T.card := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_right (s₁ := S) (s₂ := T))
        have he : T \ (S ∩ T) = T \ S := by ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
        simpa only [he] using h
      have hUcard : (T \ S).card = k - j := by omega
      have hUs : T \ S ⊆ s \ S := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨hTs (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
      refine ⟨(S ∩ T, T \ S), Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_left, hJ⟩, Finset.mem_powersetCard.mpr ⟨hUs, hUcard⟩⟩, ?_⟩
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    · intro C hC
      obtain ⟨hJ, hU⟩ := Finset.mem_product.mp hC
      rw [hleft hJ hU]
  change (∑ T ∈ V, g (S ∩ T)) = _
  rw [← hsum, Finset.sum_product]
  simp only [Finset.sum_const, ← Finset.smul_sum, Q, P, Finset.card_powersetCard]

end BoundedEdgeRegularSubgraphs
