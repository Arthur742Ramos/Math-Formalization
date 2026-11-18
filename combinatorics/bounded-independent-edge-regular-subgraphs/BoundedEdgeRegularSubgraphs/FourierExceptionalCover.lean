module

public import BoundedEdgeRegularSubgraphs.FourierBadPairCount
public import BoundedEdgeRegularSubgraphs.FourierPeaks
import Mathlib.Tactic

/-!
# Covering the few-bad-edge region outside the fixed boxes
-/

public section

open Set

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Outside the fixed phase boxes, a point with few bad edges admits a
mode, a good coordinate set of the prescribed size and an exceptional
coordinate outside that set. -/
theorem exists_exceptional_phase_coordinate (S : Finset α) (t : α → PhaseCircle)
    {η : ℝ} (hη : 0 < η) (m L : ℕ)
    (hdeg : 2 * m ≤ ((Finset.univ : Finset α) \ S).card * L)
    (hpair :
      let q := ((Finset.univ : Finset α) \ S).card - (L + 1)
      2 * m < q * (q - 1))
    (hbad : ((edgesOutsideOverlap S).filter (fun e ↦ η < ‖t e.val.1 + t e.val.2‖)).card ≤ m)
    (hout : t ∉ phaseBox 0 (10 * η) ∪ phaseBox (Real.pi : PhaseCircle) (10 * η)) :
    ∃ (b : PhaseCircle) (G : Finset α) (i : α),
      (b = 0 ∨ b = (Real.pi : PhaseCircle)) ∧ G.card = Fintype.card α - L ∧ i ∉ G ∧
        (∀ j ∈ G, ‖t j - b‖ ≤ 3 * η) ∧ 10 * η < ‖t i - b‖ := by
  classical
  have hcount := (orderedBadPairs_card_le_twice S t η).trans (Nat.mul_le_mul_left 2 hbad)
  obtain ⟨b, hb, hfar⟩ := phase_localization_of_few_bad_pairs S t hη.le L
    (hcount.trans hdeg) (hcount.trans_lt hpair)
  let B := Finset.univ.filter (fun i : α ↦ 5 * η / 2 < ‖t i - b‖)
  let T := Finset.univ \ B
  have hT : Fintype.card α - L ≤ T.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ]
    exact Nat.sub_le_sub_left hfar _
  obtain ⟨G, hGT, hG⟩ := Finset.exists_subset_card_eq hT
  have hnear (j : α) (hj : j ∈ G) : ‖t j - b‖ ≤ 5 * η / 2 := by
    have h := (Finset.mem_sdiff.mp (hGT hj)).2
    simpa only [B, Finset.mem_filter_univ, not_lt] using h
  have hi : t ∉ phaseBox b (10 * η) := by
    rcases hb with rfl | rfl
    · exact fun h ↦ hout (Or.inl h)
    · exact fun h ↦ hout (Or.inr h)
  change ¬ (∀ i, ‖t i - b‖ ≤ 10 * η) at hi
  obtain ⟨i, hi⟩ := not_forall.mp hi
  have hi' := lt_of_not_ge hi
  refine ⟨b, G, i, hb, hG, fun h ↦ ?_, fun j hj ↦ ?_, hi'⟩
  · linarith only [hi', hη, hnear i h]
  · linarith only [hnear j hj, hη]

end BoundedEdgeRegularSubgraphs
