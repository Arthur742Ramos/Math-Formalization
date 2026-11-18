module

public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Packing disjoint blocks selected before sampling
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- If every remainder of size at least half the original set contains
an admissible block, a disjoint family of admissible blocks covers more
than half of the original set. -/
theorem exists_disjoint_block_packing {α : Type*} [DecidableEq α] (s : Finset α)
    {m : ℕ} (hm : 0 < m) (P : Finset α → Prop)
    (hextract : ∀ R ⊆ s, s.card ≤ 2 * R.card → ∃ U ⊆ R, U.card = m ∧ P U) :
    ∃ B : Finset (Finset α), (∀ T ∈ B, T ⊆ s ∧ T.card = m ∧ P T) ∧
      (B : Set (Finset α)).PairwiseDisjoint id ∧ s.card < 2 * (B.card * m) := by
  classical
  let C := (s.powersetCard m).filter P
  let G := C.powerset.filter (fun B : Finset (Finset α) ↦ (B : Set (Finset α)).PairwiseDisjoint id)
  have hG₀ : (∅ : Finset (Finset α)) ∈ G := by simp [G]
  obtain ⟨B, hB, hMax⟩ := Finset.exists_max_image G Finset.card ⟨∅, hG₀⟩
  obtain ⟨hBC', hBD⟩ := Finset.mem_filter.mp hB
  have hBC : B ⊆ C := Finset.mem_powerset.mp hBC'
  have hBlock (T : Finset α) (hT : T ∈ B) : T ⊆ s ∧ T.card = m ∧ P T := by
    obtain ⟨hT₀, hP⟩ := Finset.mem_filter.mp (hBC hT)
    exact ⟨(Finset.mem_powersetCard.mp hT₀).1, (Finset.mem_powersetCard.mp hT₀).2, hP⟩
  refine ⟨B, hBlock, hBD, ?_⟩
  let F := B.biUnion id
  have hF : F ⊆ s := by
    intro i hi
    obtain ⟨T, hT, hiT⟩ := Finset.mem_biUnion.mp hi
    exact (hBlock T hT).1 hiT
  have hFcard : F.card = B.card * m := by
    rw [show F.card = ∑ T ∈ B, T.card from Finset.card_biUnion hBD]
    simp only [Finset.sum_congr rfl (fun T hT ↦ (hBlock T hT).2.1),
      Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  let R := s \ F
  have hr : R.card + F.card = s.card := Finset.card_sdiff_add_card_eq_card hF
  suffices hR : ¬ s.card ≤ 2 * R.card by omega
  intro h
  obtain ⟨U, hUR, hUm, hUP⟩ := hextract R (Finset.sdiff_subset) h
  have hUC : U ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨hUR.trans Finset.sdiff_subset, hUm⟩, hUP⟩
  have hUD (T : Finset α) (hT : T ∈ B) : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro i hiU hiT
    exact (Finset.mem_sdiff.mp (hUR hiU)).2 (Finset.mem_biUnion.mpr ⟨T, hT, hiT⟩)
  have hU : U ∉ B := by
    intro hUB
    have hself := hUD U hUB
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
    exact (Finset.disjoint_left.mp hself) hi hi
  have hNew : insert U B ∈ G := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hUC hBC), ?_⟩
    intro T hT T' hT' hne
    rcases Finset.mem_insert.mp hT with hTU | hTB
    · subst T
      have hT'B := (Finset.mem_insert.mp hT').resolve_left (Ne.symm hne)
      exact hUD T' hT'B
    · rcases Finset.mem_insert.mp hT' with hT'U | hT'B
      · subst T'
        exact (hUD T hTB).symm
      · exact hBD hTB hT'B hne
  have hlarge := hMax (insert U B) hNew
  rw [Finset.card_insert_of_notMem hU] at hlarge
  omega

end BoundedEdgeRegularSubgraphs
