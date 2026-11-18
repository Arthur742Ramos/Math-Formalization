module

public import BoundedEdgeRegularSubgraphs.FourierSymmetry
public import BoundedEdgeRegularSubgraphs.FourierLargeBad
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
# Combining the two equal Fourier peaks on the even degree lattice
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A product box centred at a mode of the degree Fourier integral. -/
def phaseBox (b : PhaseCircle) (r : ℝ) : Set (α → PhaseCircle) :=
  {t | ∀ i, ‖t i - b‖ ≤ r}

omit [LinearOrder α] in
private theorem measurableSet_phaseBox (b : PhaseCircle) (r : ℝ) :
    MeasurableSet (phaseBox (α := α) b r) := by
  have he : phaseBox (α := α) b r = ⋂ i : α, {t : α → PhaseCircle | ‖t i - b‖ ≤ r} := by
    ext t
    simp [phaseBox]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦
    measurableSet_le (((measurable_pi_apply i).sub measurable_const).norm) measurable_const)

private theorem continuous_degreeFourier (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) : Continuous (degreeFourier A q d) := by
  have hf (j : ℤ) (i : α) :
      Continuous (fun t : α → PhaseCircle ↦ fourier j (t i)) :=
    (fourier j).continuous.comp (continuous_apply i)
  unfold degreeFourier latticeCharacter edgeCharacter
  apply Continuous.mul
  · exact continuous_finsetProd _ (fun i _ ↦ hf _ i)
  · apply continuous_finsetProd
    intro e _
    exact continuous_const.add (continuous_const.mul ((hf _ _).mul (hf _ _)))

private theorem integrable_degreeFourier (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) :
    Integrable (degreeFourier A q d) phaseLaw := by
  have : IsProbabilityMeasure (phaseLaw (α := α)) := by unfold phaseLaw; infer_instance
  apply Integrable.of_bound (continuous_degreeFourier A q d).aestronglyMeasurable 1
  refine ae_of_all _ (fun t ↦ ?_)
  have h := degreeFourier_norm_le_torus_bad_count A q d t (η := 0) (lower := 0)
    le_rfl le_rfl (fun e _ ↦ mul_nonneg (q e).property.1 (sub_nonneg.mpr (q e).property.2))
  simpa using h

private noncomputable def phaseShift : (α → PhaseCircle) ≃ᵐ (α → PhaseCircle) where
  toFun t i := t i + (Real.pi : PhaseCircle)
  invFun t i := t i - (Real.pi : PhaseCircle)
  left_inv t := by funext i; exact add_sub_cancel_right _ _
  right_inv t := by funext i; exact sub_add_cancel _ _
  measurable_toFun := measurable_pi_iff.mpr (fun i ↦ (measurable_pi_apply i).add measurable_const)
  measurable_invFun := measurable_pi_iff.mpr (fun i ↦ (measurable_pi_apply i).sub measurable_const)

omit [LinearOrder α] in
private theorem measurePreserving_phaseShift :
    MeasurePreserving (phaseShift (α := α)) phaseLaw phaseLaw := by
  unfold phaseLaw
  exact measurePreserving_pi _ _ (fun _ ↦
    measurePreserving_add_right AddCircle.haarAddCircle (Real.pi : PhaseCircle))

/-- The two peak integrals coincide on the even degree lattice. -/
theorem integral_degreeFourier_pi_box_eq (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (hd : Even (∑ i, d i)) (r : ℝ) :
    (∫ t in phaseBox (Real.pi : PhaseCircle) r, degreeFourier A q d t ∂phaseLaw) =
      ∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw := by
  have he : phaseShift ⁻¹' (phaseBox (α := α) (Real.pi : PhaseCircle) r) = phaseBox 0 r := by
    ext t
    change (∀ i, ‖(t i + (Real.pi : PhaseCircle)) - (Real.pi : PhaseCircle)‖ ≤ r) ↔
      ∀ i, ‖t i - 0‖ ≤ r
    simp only [add_sub_cancel_right, sub_zero]
  have h := measurePreserving_phaseShift.setIntegral_preimage_emb phaseShift.measurableEmbedding
    (degreeFourier A q d) (phaseBox (Real.pi : PhaseCircle) r)
  rw [he] at h
  have hper (t : α → PhaseCircle) :
      degreeFourier A q d (phaseShift t) = degreeFourier A q d t :=
    degreeFourier_shift_pi A q d hd t
  simp_rw [hper] at h
  exact h.symm

omit [Fintype α] [LinearOrder α] in
private theorem phaseBox_disjoint [Nonempty α] {r : ℝ} (hr : r < Real.pi / 2) :
    Disjoint (phaseBox (α := α) 0 r) (phaseBox (Real.pi : PhaseCircle) r) := by
  rw [Set.disjoint_left]
  intro t h₁ h₂
  obtain ⟨i⟩ := ‹Nonempty α›
  have hp : ‖(Real.pi : PhaseCircle)‖ = Real.pi := by
    have h := AddCircle.norm_half_period_eq (2 * Real.pi)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
      show 2 * Real.pi / 2 = Real.pi by ring] at h
    exact h
  have h₁' : ‖t i‖ ≤ r := by simpa only [sub_zero] using h₁ i
  have h₂' : ‖t i - (Real.pi : PhaseCircle)‖ ≤ r := h₂ i
  have h := norm_sub_le (t i) (t i - (Real.pi : PhaseCircle))
  rw [sub_sub_cancel, hp] at h
  linarith

/-- Exact decomposition of an even degree atom into two equal peaks and the
remaining Fourier integral. -/
theorem probability_degreeAtom_eq_twice_peak_add_tail [Nonempty α]
    (A : Finset (Edge α)) (q : Edge α → Set.Icc (0 : ℝ) 1)
    (d : α → ℤ) (hd : Even (∑ i, d i)) {r : ℝ} (hr : r < Real.pi / 2) :
    ((graphLaw q).real (degreeAtom A d) : ℂ) =
      2 * (∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw) +
      ∫ t in (phaseBox 0 r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ, degreeFourier A q d t ∂phaseLaw := by
  let U : Set (α → PhaseCircle) := phaseBox 0 r
  let V : Set (α → PhaseCircle) := phaseBox (Real.pi : PhaseCircle) r
  have hU : MeasurableSet U := measurableSet_phaseBox _ _
  have hV : MeasurableSet V := measurableSet_phaseBox _ _
  have hf := integrable_degreeFourier A q d
  rw [probability_degreeAtom_eq_integral_degreeFourier, ← integral_add_compl (hU.union hV) hf,
    setIntegral_union (phaseBox_disjoint hr) hV hf.integrableOn hf.integrableOn,
    integral_degreeFourier_pi_box_eq A q d hd r]
  rw [two_mul (∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw)]

/-- A lower bound on one peak and an upper bound on the norm of the tail
give the corresponding finite lower bound on the even degree atom. -/
theorem probability_degreeAtom_ge_of_peak_tail [Nonempty α]
    (A : Finset (Edge α)) (q : Edge α → Set.Icc (0 : ℝ) 1)
    (d : α → ℤ) (hd : Even (∑ i, d i)) {r : ℝ} (hr : r < Real.pi / 2)
    {a b : ℝ}
    (hpeak : a ≤ (∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw).re)
    (htail : (∫ t in (phaseBox 0 r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
      ‖degreeFourier A q d t‖ ∂phaseLaw) ≤ b) :
    2 * a - b ≤ (graphLaw q).real (degreeAtom A d) := by
  let P : ℂ := ∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw
  let T : ℂ := ∫ t in (phaseBox 0 r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
    degreeFourier A q d t ∂phaseLaw
  have ht : ‖T‖ ≤ b := (norm_integral_le_integral_norm _).trans htail
  have htr : -b ≤ T.re := (neg_le_neg ht).trans (abs_le.mp (Complex.abs_re_le_norm T)).1
  have h := congrArg Complex.re (probability_degreeAtom_eq_twice_peak_add_tail A q d hd hr)
  change (((graphLaw q).real (degreeAtom A d) : ℂ)).re = (2 * P + T).re at h
  rw [Complex.ofReal_re, two_mul, Complex.add_re, Complex.add_re] at h
  change a ≤ P.re at hpeak
  linarith only [h, hpeak, htr]


end BoundedEdgeRegularSubgraphs
