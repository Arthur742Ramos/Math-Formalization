module

public import BoundedEdgeRegularSubgraphs.FourierPeaks
public import BoundedEdgeRegularSubgraphs.FourierStrongConvexity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-!
# Normalization and the real chart of the phase torus
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α]

/-- Lebesgue volume on the phase torus has mass `(2π)^k`. -/
theorem volume_phase_eq_smul_phaseLaw :
    (volume : Measure (α → PhaseCircle)) =
      ENNReal.ofReal (2 * Real.pi) ^ Fintype.card α • phaseLaw := by
  change Measure.pi (fun _ : α ↦ (volume : Measure PhaseCircle)) = _
  apply Measure.pi_eq
  intro s _
  rw [Measure.smul_apply, smul_eq_mul, phaseLaw, Measure.pi_pi]
  simp_rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Integration in the zero-centred phase box is ordinary integration in its
real chart, with exactly the normalized Haar factor. -/
theorem integral_phaseBox_zero_eq_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (α → PhaseCircle) → E) (hf : StronglyMeasurable f)
    {r : ℝ} (hr : r < Real.pi) :
    (∫ x in realPhaseBox (α := α) r, f (fun i ↦ (x i : PhaseCircle))) =
      (2 * Real.pi) ^ Fintype.card α • ∫ t in phaseBox (0 : PhaseCircle) r, f t ∂phaseLaw := by
  let I := Ioc (-Real.pi) Real.pi
  let C := {x : α → ℝ | ∀ i, x i ∈ I}
  let P (x : α → ℝ) (i : α) := (x i : PhaseCircle)
  let B := phaseBox (α := α) (0 : PhaseCircle) r
  have hB : MeasurableSet B := by
    change MeasurableSet {t : α → PhaseCircle | ∀ i, ‖t i - 0‖ ≤ r}
    rw [show {t : α → PhaseCircle | ∀ i, ‖t i - 0‖ ≤ r} =
      ⋂ i, {t : α → PhaseCircle | ‖t i - 0‖ ≤ r} by ext t; simp]
    exact MeasurableSet.iInter (fun i ↦
      measurableSet_le (((measurable_pi_apply i).sub measurable_const).norm) measurable_const)
  have hp : MeasurePreserving P (volume.restrict C) volume := by
    have h (i : α) : MeasurePreserving ((↑) : ℝ → PhaseCircle) (volume.restrict I) volume := by
      simpa only [I, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
        (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi))
    have hp' := measurePreserving_pi (fun _ : α ↦ volume.restrict I) (fun _ : α ↦ volume) h
    change MeasurePreserving P _ _ at hp'
    rw [← Measure.restrict_pi_pi (fun _ : α ↦ volume) (fun _ ↦ I)] at hp'
    have hC : C = univ.pi (fun _ ↦ I) := by ext x; simp [C]
    rw [hC]
    exact hp'
  have heq : C ∩ P ⁻¹' B = realPhaseBox (α := α) r := by
    ext x
    change ((∀ i, x i ∈ I) ∧ (∀ i, ‖P x i - 0‖ ≤ r)) ↔ ∀ i, |x i| ≤ r
    have hnorm (i : α) (hi : x i ∈ Icc (-Real.pi) Real.pi) : ‖P x i - 0‖ = |x i| := by
      rw [sub_zero]
      apply (AddCircle.norm_coe_eq_abs_iff (p := 2 * Real.pi) (by positivity)).2
      rw [abs_of_pos (show 0 < 2 * Real.pi by positivity),
        show 2 * Real.pi / 2 = Real.pi by ring]
      exact abs_le.mpr hi
    constructor
    · rintro ⟨hx, hy⟩ i
      rw [← hnorm i (Ioc_subset_Icc_self (hx i))]
      exact hy i
    · intro hx
      have hh (i : α) : x i ∈ Icc (-Real.pi) Real.pi := abs_le.mp ((hx i).trans hr.le)
      refine ⟨fun i ↦ ⟨?_, (hh i).2⟩, fun i ↦ (hnorm i (hh i)).trans_le (hx i)⟩
      exact (neg_lt_neg hr).trans_le (abs_le.mp (hx i)).1
  have h := setIntegral_map (μ := volume.restrict C) hB hf.aestronglyMeasurable
    hp.measurable.aemeasurable
  rw [hp.map_eq, Measure.restrict_restrict (hp.measurable hB), inter_comm, heq] at h
  rw [volume_phase_eq_smul_phaseLaw, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

end BoundedEdgeRegularSubgraphs
