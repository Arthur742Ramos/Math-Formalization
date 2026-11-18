module

public import BoundedEdgeRegularSubgraphs.FourierModes
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

/-!
# Counting good coordinates on the Fourier torus
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Ordered available pairs whose phase sum lies outside the `η` neighbourhood of zero. -/
noncomputable def orderedBadPairs (S : Finset α) (t : α → PhaseCircle) (η : ℝ) :
    Finset (α × α) :=
  (Finset.univ.offDiag).filter (fun uv ↦
    (uv.1 ∉ S ∨ uv.2 ∉ S) ∧ η < ‖t uv.1 + t uv.2‖)

/-- With few bad pairs, a good triangle outside the overlap anchors all but
at most `L` coordinates in the same small neighbourhood. -/
theorem phase_localization_of_few_bad_pairs (S : Finset α) (t : α → PhaseCircle)
    {η : ℝ} (hη : 0 ≤ η) (L : ℕ)
    (hdeg : (orderedBadPairs S t η).card ≤ ((Finset.univ : Finset α) \ S).card * L)
    (hpair :
      let q := ((Finset.univ : Finset α) \ S).card - (L + 1)
      (orderedBadPairs S t η).card < q * (q - 1)) :
    ∃ b : PhaseCircle, (b = 0 ∨ b = (Real.pi : PhaseCircle)) ∧
      (Finset.univ.filter (fun i : α ↦ 5 * η / 2 < ‖t i - b‖)).card ≤ L := by
  classical
  let O := (Finset.univ : Finset α) \ S
  let B := orderedBadPairs S t η
  let bad (v : α) := Finset.univ.filter (fun i ↦ (v, i) ∈ B)
  have hO : O.Nonempty := by
    apply Finset.card_pos.mp
    by_contra! h
    have hzero : O.card = 0 := by omega
    change B.card < (O.card - (L + 1)) * (O.card - (L + 1) - 1) at hpair
    simp [hzero] at hpair
  have htotal : (∑ v ∈ O, (bad v).card) ≤ B.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun z : (Σ _ : α, α) ↦ (z.1, z.2))
    · rintro ⟨v, i⟩ h
      exact (Finset.mem_filter.mp (Finset.mem_sigma.mp h).2).2
    · rintro ⟨v, i⟩ _ ⟨w, j⟩ _ h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
  obtain ⟨v, hvO, hv⟩ : ∃ v ∈ O, (bad v).card ≤ L := by
    by_contra! h
    have hs := Finset.sum_lt_sum_of_nonempty hO (fun v hv ↦ h v hv)
    rw [Finset.sum_const, nsmul_eq_mul] at hs
    exact hs.not_ge (htotal.trans hdeg)
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hvO).2
  let G := (O.erase v).filter (fun i ↦ ‖t v + t i‖ ≤ η)
  have hnot (i : α) (hiv : i ≠ v) (hi : η < ‖t v + t i‖) : i ∈ bad v := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, hiv.symm⟩, Or.inl hvS, hi⟩
  have hcard : O.card - (L + 1) ≤ G.card := by
    have hsub : ((O.erase v).filter fun i ↦ ¬ ‖t v + t i‖ ≤ η) ⊆ bad v := by
      intro i hi
      obtain ⟨hmem, hnorm⟩ := Finset.mem_filter.mp hi
      exact hnot i (Finset.ne_of_mem_erase hmem) (lt_of_not_ge hnorm)
    have hs := Finset.card_filter_add_card_filter_not (s := O.erase v)
      (p := fun i ↦ ‖t v + t i‖ ≤ η)
    change G.card + ((O.erase v).filter fun i ↦ ¬ ‖t v + t i‖ ≤ η).card =
      (O.erase v).card at hs
    rw [Finset.card_erase_of_mem hvO] at hs
    have hu := (Finset.card_le_card hsub).trans hv
    omega
  obtain ⟨a, b, haG, hbG, hab⟩ : ∃ a b : α, a ∈ G ∧ b ∈ G ∧ ‖t a + t b‖ ≤ η := by
    by_contra! h
    have hsub : G.offDiag ⊆ B := by
      rintro ⟨i, j⟩ hij
      obtain ⟨hi, hj, hne⟩ := Finset.mem_offDiag.mp hij
      have hiO := Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩,
        Or.inl (Finset.mem_sdiff.mp hiO).2, h i j hi hj⟩
    have hp := Finset.card_le_card hsub
    rw [Finset.offDiag_card, ← Nat.mul_sub_one] at hp
    exact hpair.not_ge ((Nat.mul_le_mul hcard (Nat.sub_le_sub_right hcard 1)).trans hp)
  obtain ⟨c, hc, hvc⟩ := phase_good_triangle (t v) (t a) (t b)
    (Finset.mem_filter.mp haG).2 (Finset.mem_filter.mp hbG).2 hab
  refine ⟨c, hc, ?_⟩
  apply (Finset.card_le_card ?_).trans hv
  intro i hi
  obtain ⟨_, hnorm⟩ := Finset.mem_filter.mp hi
  have hiv : i ≠ v := by
    rintro rfl
    linarith
  apply hnot i hiv
  by_contra! hh
  exact hnorm.not_ge (phase_good_neighbour (t v) (t i) c hc hvc hh)

end BoundedEdgeRegularSubgraphs
