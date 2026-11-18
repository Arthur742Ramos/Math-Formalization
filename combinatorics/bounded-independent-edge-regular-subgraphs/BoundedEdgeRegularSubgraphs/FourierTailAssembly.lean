module

public import BoundedEdgeRegularSubgraphs.FourierPhaseAnnulus
public import BoundedEdgeRegularSubgraphs.FourierTailAbsorption
import Mathlib.Tactic

/-!
# Combining the exterior and annulus bounds
-/

public section

open Set MeasureTheory

namespace BoundedEdgeRegularSubgraphs

private theorem setIntegral_union_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x) (s t : Set X) :
    (∫ x in s ∪ t, f x ∂μ) ≤ (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  have hs : Integrable f (μ.restrict s) := hf.integrableOn
  have ht : Integrable f (μ.restrict t) := hf.integrableOn
  have h := integral_mono_measure (Measure.restrict_union_le (μ := μ) s t)
    (ae_of_all _ hf₀) (hs.add_measure ht)
  rwa [integral_add_measure hs ht] at h

/-- The finite combination behind Lemma B.1. Only the exterior and
the mass in the two small boxes enter as integral estimates. -/
theorem integral_degreeFourier_outside_small_boxes_le {n : ℕ}
    (S : Finset (Fin (n + 1))) (hm : 3 ≤ ((Finset.univ : Finset (Fin (n + 1))) \ S).card)
    (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (d : Fin (n + 1) → ℤ)
    {l κ R r : ℝ} (hl : 0 ≤ l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (hκ : 0 ≤ κ) (hκ' : κ ≤ l * ((((Finset.univ : Finset (Fin (n + 1))) \ S).card : ℝ) ^ 2 /
      (3 * Fintype.card (Fin (n + 1)))) / 2) (hR : 2 * R ≤ Real.pi / 3) (hr : 0 ≤ r)
    {X C a a₀ : ℝ} (ha : 0 ≤ a)
    (hsmall : a + 2 * (n + 1) * Real.exp (-κ * r ^ 2 / 2) ≤ 1 / 2)
    (hP : (∫ t in phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r,
      ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) ≤ C * X)
    (hT : (∫ t in (phaseBox (0 : PhaseCircle) R ∪ phaseBox (Real.pi : PhaseCircle) R)ᶜ,
      ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) ≤
        a₀ + a * ∫ t, ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) :
    (∫ t in (phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
      ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) ≤
      a₀ + 2 * (a + 2 * (n + 1) * Real.exp (-κ * r ^ 2 / 2)) * (C * X + a₀) := by
  let A := edgesOutsideOverlap S
  let f (t : Fin (n + 1) → PhaseCircle) := ‖degreeFourier A q d t‖
  let U := phaseBox (α := Fin (n + 1)) (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r
  let T := (phaseBox (α := Fin (n + 1)) (0 : PhaseCircle) R ∪ phaseBox (Real.pi : PhaseCircle) R)ᶜ
  let N₀ := phaseBox (α := Fin (n + 1)) (0 : PhaseCircle) R \ phaseBox (0 : PhaseCircle) r
  let N₁ := phaseBox (α := Fin (n + 1)) (Real.pi : PhaseCircle) R \ phaseBox (Real.pi : PhaseCircle) r
  let J := ∫ t, f t ∂phaseLaw
  let P := ∫ t in U, f t ∂phaseLaw
  let Z := ∫ t in T, f t ∂phaseLaw
  let N := (∫ t in N₀, f t ∂phaseLaw) + ∫ t in N₁, f t ∂phaseLaw
  let b := 2 * (n + 1 : ℝ) * Real.exp (-κ * r ^ 2 / 2)
  have hf : Integrable f phaseLaw := (integrable_degreeFourier A q d).norm
  have hf₀ (t : Fin (n + 1) → PhaseCircle) : 0 ≤ f t := norm_nonneg _
  have hU : MeasurableSet U := (measurableSet_phaseBox _ _).union (measurableSet_phaseBox _ _)
  have hcover : Uᶜ ⊆ T ∪ (N₀ ∪ N₁) := by
    intro t ht
    by_cases h : t ∈ T
    · exact Or.inl h
    · have h' : t ∈ phaseBox (α := Fin (n + 1)) 0 R ∪ phaseBox (Real.pi : PhaseCircle) R := not_not.mp h
      exact Or.inr (h'.elim (fun h₀ ↦ Or.inl ⟨h₀, fun hh ↦ ht (Or.inl hh)⟩)
        (fun h₁ ↦ Or.inr ⟨h₁, fun hh ↦ ht (Or.inr hh)⟩))
  have htail : (∫ t in Uᶜ, f t ∂phaseLaw) ≤ Z + N := by
    calc
      _ ≤ ∫ t in T ∪ (N₀ ∪ N₁), f t ∂phaseLaw :=
        setIntegral_mono_set hf.integrableOn (ae_of_all _ hf₀) (ae_of_all _ hcover)
      _ ≤ Z + (∫ t in N₀ ∪ N₁, f t ∂phaseLaw) := setIntegral_union_le hf hf₀ _ _
      _ ≤ _ := add_le_add_right (setIntegral_union_le hf hf₀ N₀ N₁) Z
  have hsplit : J ≤ P + Z + N := by
    have h := integral_add_compl hU hf
    change P + _ = J at h
    linarith only [h, htail]
  have hN : N ≤ b * J := by
    have h := integral_phase_annulus_zero_le S hm q d hl hq hκ hκ' hR hr
    have h₀ := setIntegral_le_integral (s := phaseBox (0 : PhaseCircle) R) hf (ae_of_all _ hf₀)
    have hπ : (∫ t in N₁, f t ∂phaseLaw) = ∫ t in N₀, f t ∂phaseLaw :=
      integral_phase_annulus_pi_eq_zero A q d R r
    have h' := h.trans (mul_le_mul_of_nonneg_left h₀ (by positivity))
    change _ ≤ ((n : ℝ) + 1) * Real.exp (-κ * r ^ 2 / 2) * J at h'
    dsimp only [N, b]
    rw [hπ]
    linarith only [h']
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  exact htail.trans (fourier_tail_absorption hsplit hP hT hN ha hb hsmall (integral_nonneg hf₀))

end BoundedEdgeRegularSubgraphs
