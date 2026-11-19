module

public import BoundedEdgeRegularSubgraphs.FourierLocalization
public import BoundedEdgeRegularSubgraphs.FourierLargeBad
import Mathlib.Tactic

/-!
# Counting the two orientations of bad edges
-/

public section

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The ordered count for the localisation argument is at most twice the
edge count for the exponential bound on the integrand. -/
theorem orderedBadPairs_card_le_twice (S : Finset α) (t : α → PhaseCircle) (η : ℝ) :
    (orderedBadPairs S t η).card ≤
      2 * ((edgesOutsideOverlap S).filter (fun e ↦ η < ‖t e.val.1 + t e.val.2‖)).card := by
  classical
  let T := orderedBadPairs S t η
  let B := (edgesOutsideOverlap S).filter (fun e ↦ η < ‖t e.val.1 + t e.val.2‖)
  have hT (p : T) : p.val.1 ≠ p.val.2 :=
    (Finset.mem_offDiag.mp (Finset.mem_filter.mp p.property).1).2.2
  let g (p : T) : Edge α × Bool :=
    (⟨(min p.val.1 p.val.2, max p.val.1 p.val.2), min_lt_max.mpr (hT p)⟩,
      decide (p.val.1 < p.val.2))
  have hmaps : Set.MapsTo g (T.attach : Set T)
      ((B ×ˢ (Finset.univ : Finset Bool) : Finset (Edge α × Bool)) : Set (Edge α × Bool)) := by
    intro p _
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩,
      Finset.mem_univ _⟩
    · have hp := (Finset.mem_filter.mp p.property).2.1
      change ¬ (min p.val.1 p.val.2 ∈ S ∧ max p.val.1 p.val.2 ∈ S)
      rcases le_total p.val.1 p.val.2 with h | h
      · simpa only [min_eq_left h, max_eq_right h, not_and_or] using hp
      · simpa only [min_eq_right h, max_eq_left h, not_and_or, or_comm] using hp
    · have hp := (Finset.mem_filter.mp p.property).2.2
      change η < ‖t (min p.val.1 p.val.2) + t (max p.val.1 p.val.2)‖
      rcases le_total p.val.1 p.val.2 with h | h
      · simpa only [min_eq_left h, max_eq_right h] using hp
      · simpa only [min_eq_right h, max_eq_left h, add_comm] using hp
  have hinj : Function.Injective g := by
    intro p q h
    let recover (v : Edge α × Bool) := if v.2 then v.1.val else v.1.val.swap
    have hr (p : T) : recover (g p) = p.val := by
      rcases lt_or_gt_of_ne (hT p) with h' | h'
      · simp [recover, g, h', min_eq_left h'.le, max_eq_right h'.le]
      · simp [recover, g, h'.not_gt, min_eq_right h'.le, max_eq_left h'.le]
    exact Subtype.ext (by simpa only [hr] using congrArg recover h)
  have h := Finset.card_le_card_of_injOn g hmaps hinj.injOn
  rw [Finset.card_attach, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm] at h
  exact h

end BoundedEdgeRegularSubgraphs
