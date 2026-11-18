module

public import BoundedEdgeRegularSubgraphs.FourierStrongConvexity
public import BoundedEdgeRegularSubgraphs.StrongConvexMarginal
public import BoundedEdgeRegularSubgraphs.FourierLargeBad
import Mathlib.Tactic

/-!
# Coordinate tails inside the real Fourier box
-/

public section

open MeasureTheory Set

namespace BoundedEdgeRegularSubgraphs

private theorem realPhaseBox_eq_Icc {ι : Type*} (r : ℝ) :
    realPhaseBox (α := ι) r = Icc (fun _ ↦ -r) (fun _ ↦ r) := by
  ext x
  change (∀ i, |x i| ≤ r) ↔ (∀ i, -r ≤ x i) ∧ (∀ i, x i ≤ r)
  simp only [abs_le, forall_and]

/-- The mass of one coordinate tail on the real box in Lemma B.1,
for the full and deleted-clique instances together. -/
theorem integral_realFourierBox_coordinate_tail_le {n : ℕ}
    (S : Finset (Fin (n + 1))) (hm : 3 ≤ ((Finset.univ : Finset (Fin (n + 1))) \ S).card)
    (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (i : Fin (n + 1)) {l κ R r : ℝ}
    (hl : 0 ≤ l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (hκ : 0 ≤ κ) (hκ' : κ ≤ l * ((((Finset.univ : Finset (Fin (n + 1))) \ S).card : ℝ) ^ 2 /
      (3 * Fintype.card (Fin (n + 1)))) / 2)
    (hR : 2 * R ≤ Real.pi / 3) (hr : 0 ≤ r) :
    let C := realPhaseBox (α := Fin (n + 1)) R
    let V := degreeFourierPotential (edgesOutsideOverlap S) q
    (∫ x in C ∩ {x | r < |x i|}, Real.exp (-V x)) ≤
      Real.exp (-κ * r ^ 2 / 2) * ∫ x in C, Real.exp (-V x) := by
  let C := realPhaseBox (α := Fin (n + 1)) R
  let V := degreeFourierPotential (edgesOutsideOverlap S) q
  let P := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  let D := P ⁻¹' C
  let W := V ∘ P
  have hp : MeasurePreserving P :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  have hpdef (p : ℝ × (Fin n → ℝ)) : P p = i.insertNth p.1 p.2 := rfl
  have hp₁ (p : ℝ × (Fin n → ℝ)) : P p i = p.1 := by rw [hpdef, Fin.insertNth_apply_same]
  have hp₂ (p : ℝ × (Fin n → ℝ)) (j : Fin n) : P p (i.succAbove j) = p.2 j := by
    rw [hpdef, Fin.insertNth_apply_succAbove]
  let L : (ℝ × (Fin n → ℝ)) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
    { toFun := P
      map_add' := fun p p' ↦ funext (i.forall_iff_succAbove.2
        ⟨by simp [hp₁], fun j ↦ by simp [hp₂]⟩)
      map_smul' := fun c p ↦ funext (i.forall_iff_succAbove.2
        ⟨by simp [hp₁], fun j ↦ by simp [hp₂]⟩) }
  have hC : IsCompact C := by rw [show C = _ from realPhaseBox_eq_Icc R]; exact isCompact_Icc
  have hD : MeasurableSet D := P.measurable hC.measurableSet
  have hW : Measurable W := by
    apply Measurable.comp _ P.measurable
    unfold V degreeFourierPotential fourierPotential fourierEnvelope
    apply Finset.measurable_sum
    intro e _
    fun_prop
  have hconv := (convexOn_degreeFourierPotential_sub_coordinate_sq S hm q i hl hq hκ hκ' hR).comp_linearMap L
  have hconv' : ConvexOn ℝ D (fun p ↦ W p - κ * p.1 ^ 2 / 2) := by
    have hfun : (fun t ↦ V t - κ * t i ^ 2 / 2) ∘ L =
        (fun p ↦ W p - κ * p.1 ^ 2 / 2) := by
      funext p
      change V (P p) - κ * (P p i) ^ 2 / 2 = V (P p) - κ * p.1 ^ 2 / 2
      rw [hp₁]
    change ConvexOn ℝ D ((fun t ↦ V t - κ * t i ^ 2 / 2) ∘ L) at hconv
    rwa [hfun] at hconv
  have hDneg (p : ℝ × (Fin n → ℝ)) : -p ∈ D ↔ p ∈ D := by
    change (∀ j, |L (-p) j| ≤ R) ↔ ∀ j, |L p j| ≤ R
    simp only [map_neg, Pi.neg_apply, abs_neg]
  have hWneg (p : ℝ × (Fin n → ℝ)) (_ : p ∈ D) : W (-p) = W p := by
    change V (L (-p)) = V (L p)
    rw [map_neg]
    exact degreeFourierPotential_even _ _ (L p)
  have hb (p : ℝ × (Fin n → ℝ)) (h : p ∈ D) : ‖Real.exp (-W p)‖ ≤ 1 := by
    have hx (j : Fin (n + 1)) : |P p j| ≤ R := h j
    have hx' (e : Edge (Fin (n + 1))) :
        |P p e.val.1 + P p e.val.2| ≤ Real.pi / 3 :=
      (abs_add_le _ _).trans (by linarith only [hx e.val.1, hx e.val.2, hR])
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    change Real.exp (-V (P p)) ≤ 1
    rw [← degreeFourier_norm_eq_exp_neg_potential _ q (fun _ ↦ 0) _ (fun e _ ↦ hx' e)]
    have hz := degreeFourier_norm_le_torus_bad_count (edgesOutsideOverlap S) q (fun _ ↦ 0)
      (fun j ↦ (P p j : PhaseCircle)) (η := 0) (lower := 0) le_rfl le_rfl
      (fun e _ ↦ (hl.trans (hq e)))
    simpa using hz
  have hI : Integrable (D.indicator (fun p ↦ Real.exp (-W p))) volume := by
    rw [integrable_indicator_iff hD]
    have hmass : volume D = volume C := hp.measure_preimage (s := C) hC.measurableSet.nullMeasurableSet
    exact Measure.integrableOn_of_bounded (M := 1) (hmass.trans_ne hC.measure_lt_top.ne)
      (Real.measurable_exp.comp hW.neg).aestronglyMeasurable
      ((ae_restrict_iff' hD).2 (ae_of_all _ hb))
  have hIslice (t : ℝ) :
      Integrable (fun x ↦ D.indicator (fun p ↦ Real.exp (-W p)) (t, x)) := by
    let D' := (fun x : Fin n → ℝ ↦ (t, x)) ⁻¹' D
    have hd' : MeasurableSet D' := (measurable_const.prodMk measurable_id) hD
    have hsub : D' ⊆ realPhaseBox (α := Fin n) R := by
      intro x hx j
      have hh : |P (t, x) (i.succAbove j)| ≤ R := hx (i.succAbove j)
      rwa [hp₂] at hh
    have hc' : IsCompact (realPhaseBox (α := Fin n) R) := by
      rw [realPhaseBox_eq_Icc]
      exact isCompact_Icc
    change Integrable (D'.indicator (fun x ↦ Real.exp (-W (t, x))))
    rw [integrable_indicator_iff hd']
    apply Measure.integrableOn_of_bounded (M := 1)
      ((measure_mono hsub).trans_lt hc'.measure_lt_top).ne
      ((Real.measurable_exp.comp hW.neg).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact (ae_restrict_iff' hd').2 (ae_of_all _ (fun x hx ↦ hb (t, x) hx))
  have h := integral_coordinate_tail_le_of_convex_tilt D hD W hW hκ hr hconv' hDneg hWneg hI hIslice
  have hleft :
      (∫ p in D ∩ {p | r < |p.1|}, Real.exp (-W p)) =
        (∫ x in C ∩ {x | r < |x i|}, Real.exp (-V x)) := by
    have heq : D ∩ {p | r < |p.1|} = P ⁻¹' (C ∩ {x | r < |x i|}) := by
      ext p
      simp [D, hp₁]
    rw [heq]
    simpa only [W, Function.comp_apply] using hp.setIntegral_preimage_emb P.measurableEmbedding
      (fun x ↦ Real.exp (-V x)) (C ∩ {x | r < |x i|})
  have hright : (∫ p in D, Real.exp (-W p)) = ∫ x in C, Real.exp (-V x) := by
    simpa only [D, W, Function.comp_apply] using
      hp.setIntegral_preimage_emb P.measurableEmbedding (fun x ↦ Real.exp (-V x)) C
  rw [hleft, hright] at h
  exact h

end BoundedEdgeRegularSubgraphs
