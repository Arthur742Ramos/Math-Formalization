module

public import BoundedEdgeRegularSubgraphs.FourierRealBoxTail
public import BoundedEdgeRegularSubgraphs.FourierVolume
import Mathlib.Tactic

/-!
# The annulus between the fixed and shrinking Fourier boxes
-/

public section

open Set MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- A finite cover bounds an integral of a nonnegative function by the
sum of the integrals over the covering sets. -/
theorem setIntegral_iUnion_le_of_nonneg {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x)
    (E : ι → Set X) (hE : ∀ i, MeasurableSet (E i)) :
    (∫ x in ⋃ i, E i, f x ∂μ) ≤ ∑ i, ∫ x in E i, f x ∂μ := by
  classical
  rw [← integral_indicator (MeasurableSet.iUnion hE)]
  simp_rw [← integral_indicator (hE _)]
  rw [← integral_finsetSum _ (fun i _ ↦ hf.indicator (hE i))]
  apply integral_mono (hf.indicator (MeasurableSet.iUnion hE))
    (integrable_finsetSum _ (fun i _ ↦ hf.indicator (hE i)))
  intro x
  by_cases hx : x ∈ ⋃ i, E i
  · rw [indicator_of_mem hx]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have h := Finset.single_le_sum
      (f := fun i ↦ (E i).indicator f x) (fun i _ ↦ indicator_nonneg (fun x _ ↦ hf₀ x) _)
      (Finset.mem_univ i)
    rwa [indicator_of_mem hi] at h
  · rw [indicator_of_notMem hx]
    exact Finset.sum_nonneg (fun i _ ↦ indicator_nonneg (fun x _ ↦ hf₀ x) _)

/-- The torus annulus in the zero-centred mode has mass at most
`k exp(-κ r²/2)` times the mass of the fixed box. -/
theorem integral_phase_annulus_zero_le {n : ℕ}
    (S : Finset (Fin (n + 1))) (hm : 3 ≤ ((Finset.univ : Finset (Fin (n + 1))) \ S).card)
    (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (d : Fin (n + 1) → ℤ) {l κ R r : ℝ}
    (hl : 0 ≤ l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (hκ : 0 ≤ κ) (hκ' : κ ≤ l * ((((Finset.univ : Finset (Fin (n + 1))) \ S).card : ℝ) ^ 2 /
      (3 * Fintype.card (Fin (n + 1)))) / 2)
    (hR : 2 * R ≤ Real.pi / 3) (hr : 0 ≤ r) :
    let f := fun t ↦ ‖degreeFourier (edgesOutsideOverlap S) q d t‖
    (∫ t in phaseBox (0 : PhaseCircle) R \ phaseBox (0 : PhaseCircle) r, f t ∂phaseLaw) ≤
      (n + 1 : ℝ) * Real.exp (-κ * r ^ 2 / 2) *
        ∫ t in phaseBox (0 : PhaseCircle) R, f t ∂phaseLaw := by
  let A := edgesOutsideOverlap S
  let f (t : Fin (n + 1) → PhaseCircle) := ‖degreeFourier A q d t‖
  let C := realPhaseBox (α := Fin (n + 1)) R
  let B := phaseBox (α := Fin (n + 1)) (0 : PhaseCircle) R
  let E (i : Fin (n + 1)) := {t : Fin (n + 1) → PhaseCircle | r < ‖t i‖}
  let P (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) := (x i : PhaseCircle)
  let g (x : Fin (n + 1) → ℝ) := Real.exp (-degreeFourierPotential A q x)
  let scale : ℝ := (2 * Real.pi) ^ Fintype.card (Fin (n + 1))
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hRπ : R < Real.pi := by linarith only [hR, Real.pi_pos]
  have hB : MeasurableSet B := measurableSet_phaseBox _ _
  have hC : MeasurableSet C := by
    rw [show C = ⋂ i : Fin (n + 1), {x : Fin (n + 1) → ℝ | |x i| ≤ R} by
      ext x; simp [C, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hE (i : Fin (n + 1)) : MeasurableSet (E i) :=
    measurableSet_lt measurable_const (measurable_pi_apply i).norm
  have hF : StronglyMeasurable f := (continuous_degreeFourier A q d).norm.stronglyMeasurable
  have hI : Integrable f phaseLaw := (integrable_degreeFourier A q d).norm
  have hfg (x : Fin (n + 1) → ℝ) (hx : x ∈ C) : f (P x) = g x := by
    apply degreeFourier_norm_eq_exp_neg_potential
    intro e _
    exact (abs_add_le _ _).trans (by linarith only [hx e.val.1, hx e.val.2, hR])
  have hP (x : Fin (n + 1) → ℝ) (hx : x ∈ C) (i : Fin (n + 1)) :
      ‖P x i‖ = |x i| := by
    apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
    rw [abs_of_pos (show 0 < 2 * Real.pi by positivity), show 2 * Real.pi / 2 = Real.pi by ring]
    exact (hx i).trans hRπ.le
  have hmass : (∫ x in C, g x) = scale * ∫ t in B, f t ∂phaseLaw := by
    have h := integral_phaseBox_zero_eq_real f hF hRπ
    rw [smul_eq_mul] at h
    exact (setIntegral_congr_fun hC (fun x hx ↦ (hfg x hx).symm)).trans h
  have hcoord (i : Fin (n + 1)) :
      (∫ x in C ∩ {x | r < |x i|}, g x) = scale * ∫ t in B ∩ E i, f t ∂phaseLaw := by
    have h := integral_phaseBox_zero_eq_real ((E i).indicator f) (hF.indicator (hE i)) hRπ
    rw [smul_eq_mul, setIntegral_indicator (hE i)] at h
    change (∫ x in C, (E i).indicator f (P x)) = _ at h
    have hx : MeasurableSet {x : Fin (n + 1) → ℝ | r < |x i|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_pi_apply i))
    rw [← setIntegral_indicator hx, ← h]
    apply setIntegral_congr_fun hC
    intro x hx
    have he : P x ∈ E i ↔ r < |x i| := by change r < ‖P x i‖ ↔ _; rw [hP x hx i]
    by_cases hi : r < |x i|
    · have hmem : x ∈ {y : Fin (n + 1) → ℝ | r < |y i|} := hi
      rw [indicator_of_mem hmem]
      exact ((indicator_of_mem (he.mpr hi) f).trans (hfg x hx)).symm
    · have hmem : x ∉ {y : Fin (n + 1) → ℝ | r < |y i|} := hi
      rw [indicator_of_notMem hmem]
      exact (indicator_of_notMem (show P x ∉ E i from fun hz ↦ hi (he.mp hz)) f).symm
  have hbound (i : Fin (n + 1)) : (∫ t in B ∩ E i, f t ∂phaseLaw) ≤
      Real.exp (-κ * r ^ 2 / 2) * ∫ t in B, f t ∂phaseLaw := by
    have h := integral_realFourierBox_coordinate_tail_le S hm q i hl hq hκ hκ' hR hr
    change (∫ x in C ∩ {x | r < |x i|}, g x) ≤
      Real.exp (-κ * r ^ 2 / 2) * ∫ x in C, g x at h
    rw [hcoord, hmass] at h
    apply le_of_mul_le_mul_left _ hscale
    linarith only [h]
  have hset : phaseBox (0 : PhaseCircle) R \ phaseBox (0 : PhaseCircle) r = ⋃ i, B ∩ E i := by
    ext t
    simp only [mem_sdiff, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      change ¬ (∀ i, ‖t i - 0‖ ≤ r) at h₂
      obtain ⟨i, hi⟩ := not_forall.mp h₂
      exact ⟨i, h₁, by simpa only [E, mem_setOf_eq, sub_zero] using (lt_of_not_ge hi)⟩
    · rintro ⟨i, h₁, h₂⟩
      refine ⟨h₁, fun hp ↦ ?_⟩
      have hi : ‖t i‖ ≤ r := by simpa only [sub_zero] using hp i
      exact (show r < ‖t i‖ from h₂).not_ge hi
  change (∫ t in phaseBox (0 : PhaseCircle) R \ phaseBox (0 : PhaseCircle) r, f t ∂phaseLaw) ≤
    (n + 1 : ℝ) * Real.exp (-κ * r ^ 2 / 2) * ∫ t in B, f t ∂phaseLaw
  rw [hset]
  calc
    _ ≤ ∑ i, ∫ t in B ∩ E i, f t ∂phaseLaw :=
      setIntegral_iUnion_le_of_nonneg hI (fun _ ↦ norm_nonneg _) _ (fun i ↦ hB.inter (hE i))
    _ ≤ ∑ _ : Fin (n + 1), Real.exp (-κ * r ^ 2 / 2) * ∫ t in B, f t ∂phaseLaw :=
      Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, mul_assoc]

/-- The π shift preserves the modulus for every target degree vector. -/
theorem integral_phase_annulus_pi_eq_zero {α : Type*} [Fintype α] [LinearOrder α]
    (A : Finset (Edge α)) (q : Edge α → Icc (0 : ℝ) 1) (d : α → ℤ) (R r : ℝ) :
    (∫ t in phaseBox (Real.pi : PhaseCircle) R \ phaseBox (Real.pi : PhaseCircle) r,
      ‖degreeFourier A q d t‖ ∂phaseLaw) =
    ∫ t in phaseBox 0 R \ phaseBox 0 r, ‖degreeFourier A q d t‖ ∂phaseLaw := by
  let b : α → PhaseCircle := fun _ ↦ (Real.pi : PhaseCircle)
  let e := (Homeomorph.addRight b).toMeasurableEquiv
  have he : MeasurePreserving e phaseLaw phaseLaw :=
    measurePreserving_pi _ _ (fun _ ↦ measurePreserving_add_right AddCircle.haarAddCircle _)
  have hbox (u : ℝ) : e ⁻¹' phaseBox (Real.pi : PhaseCircle) u = phaseBox 0 u := by
    ext t
    change (∀ i, ‖(t i + (Real.pi : PhaseCircle)) - (Real.pi : PhaseCircle)‖ ≤ u) ↔
      ∀ i, ‖t i - 0‖ ≤ u
    simp only [add_sub_cancel_right, sub_zero]
  have hmod (t : α → PhaseCircle) : ‖degreeFourier A q d (e t)‖ = ‖degreeFourier A q d t‖ := by
    have hπ : (Real.pi : PhaseCircle) + (Real.pi : PhaseCircle) = 0 := by
      rw [← AddCircle.coe_add, ← two_mul, AddCircle.coe_period]
    rw [degreeFourier_norm_eq_phase_product, degreeFourier_norm_eq_phase_product]
    apply Finset.prod_congr rfl
    intro v _
    have hsum : (t v.val.1 + (Real.pi : PhaseCircle)) + (t v.val.2 + (Real.pi : PhaseCircle)) =
        t v.val.1 + t v.val.2 := by
      rw [add_add_add_comm, hπ, add_zero]
    change ‖phaseBernoulliFactor (q v) ((t v.val.1 + (Real.pi : PhaseCircle)) +
      (t v.val.2 + (Real.pi : PhaseCircle)))‖ = _
    rw [hsum]
  have h := he.setIntegral_preimage_emb e.measurableEmbedding (fun t ↦ ‖degreeFourier A q d t‖)
    (phaseBox (Real.pi : PhaseCircle) R \ phaseBox (Real.pi : PhaseCircle) r)
  rw [preimage_sdiff, hbox R, hbox r] at h
  simp_rw [hmod] at h
  exact h.symm

end BoundedEdgeRegularSubgraphs
