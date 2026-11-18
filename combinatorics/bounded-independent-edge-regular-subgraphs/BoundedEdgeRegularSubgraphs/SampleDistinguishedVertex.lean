module

public import BoundedEdgeRegularSubgraphs.SamplingMoments
import Mathlib.Tactic

/-!
# Conditioning a uniform sample on a distinguished vertex
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

/-- Rearranging the sample sum by its distinguished vertex leaves a
uniform sample of order one less among the other vertices. -/
theorem sum_samples_distinguished_vertex {M : Type*} [AddCommMonoid M]
    (s : Finset α) {k : ℕ} (hk : 0 < k) (f : α → Finset α → M) :
    (∑ S ∈ s.powersetCard k, ∑ i ∈ S, f i (S.erase i)) =
      ∑ i ∈ s, ∑ T ∈ (s.erase i).powersetCard (k - 1), f i T := by
  classical
  have h₁ : ∀ S ∈ s.powersetCard k, (∑ i ∈ S, f i (S.erase i)) =
      ∑ i ∈ s, if i ∈ S then f i (S.erase i) else 0 := by
    intro S hS
    rw [← Finset.sum_filter, show s.filter (fun i ↦ i ∈ S) = S by
      ext i
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hi ↦ (Finset.mem_powersetCard.mp hS).1 hi)]
  rw [Finset.sum_congr rfl h₁, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun T _ ↦ insert i T) ?_ ?_ ?_ ?_
  · intro T hT
    have ht := Finset.mem_powersetCard.mp hT
    have hnot : i ∉ T := fun h ↦ Finset.notMem_erase i s (ht.1 h)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self i T⟩
    · exact Finset.insert_subset hi (ht.1.trans (Finset.erase_subset _ _))
    · rw [Finset.card_insert_of_notMem hnot, ht.2]
      omega
  · intro T hT T' hT' he
    have hn : i ∉ T := fun h ↦ Finset.notMem_erase i s ((Finset.mem_powersetCard.mp hT).1 h)
    have hn' : i ∉ T' := fun h ↦ Finset.notMem_erase i s ((Finset.mem_powersetCard.mp hT').1 h)
    have h := congrArg (fun S : Finset α ↦ S.erase i) he
    simpa only [Finset.erase_insert hn, Finset.erase_insert hn'] using h
  · intro S hS
    obtain ⟨h₀, hSi⟩ := Finset.mem_filter.mp hS
    have hs := Finset.mem_powersetCard.mp h₀
    refine ⟨S.erase i, Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase _ hs.1, ?_⟩, ?_⟩
    · rw [Finset.card_erase_of_mem hSi, hs.2]
    · exact Finset.insert_erase hSi
  · intro T hT
    have hn : i ∉ T := fun h ↦ Finset.notMem_erase i s ((Finset.mem_powersetCard.mp hT).1 h)
    rw [Finset.erase_insert hn]

/-- Counting pairs consisting of a sample and a distinguished vertex,
with the vertex marked in either order. -/
theorem card_mul_choose_pred (s : Finset α) {k : ℕ} (hk : 0 < k) :
    k * s.card.choose k = s.card * (s.card - 1).choose (k - 1) := by
  have h := sum_samples_distinguished_vertex s hk (M := ℕ) (fun _ _ ↦ 1)
  have hL (S : Finset α) (hS : S ∈ s.powersetCard k) : (∑ _i ∈ S, (1 : ℕ)) = k := by
    simp [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hL] at h
  have hR (i : α) (hi : i ∈ s) : (∑ _T ∈ (s.erase i).powersetCard (k - 1), (1 : ℕ)) =
      (s.card - 1).choose (k - 1) := by
    simp [Finset.card_powersetCard, Finset.card_erase_of_mem hi]
  rw [Finset.sum_congr rfl hR] at h
  simpa [Finset.card_powersetCard, Nat.mul_comm] using h

end BoundedEdgeRegularSubgraphs
