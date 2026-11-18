module

public import BoundedEdgeRegularSubgraphs.FourierCoordinateFiber
public import BoundedEdgeRegularSubgraphs.FourierPeaks
public import BoundedEdgeRegularSubgraphs.EdgeNeighbours
import Mathlib.Tactic

/-!
# Replacing an exceptional phase coordinate
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- For one coordinate outside the fixed box, a replacement close to the
mode improves each edge to the good coordinates and controls the others. -/
theorem degreeFourier_exceptional_update_le
    (A : Finset (Edge α)) (G : Finset α) (q : Edge α → Icc (0 : ℝ) 1) (d : α → ℤ)
    (t : α → PhaseCircle) (i : α) (b z : PhaseCircle) {η γ r : ℝ}
    (hr : 0 < r) (hx : 10 * η ≤ ‖t i - b‖)
    (hgood : ∀ j ∈ G, ‖t j - b‖ ≤ 3 * η) (hz : ‖z - b‖ ≤ η)
    (hcompare : ∀ e ∈ A, ∀ x y w : PhaseCircle,
      10 * η ≤ ‖x - b‖ → ‖y - b‖ ≤ 3 * η → ‖w - b‖ ≤ η →
        ‖phaseBernoulliFactor (q e) (x + y)‖ ≤
          Real.exp (-γ) * ‖phaseBernoulliFactor (q e) (w + y)‖)
    (havoid : ∀ e ∈ incidentEdges A i, otherEndpoint i e ∉ G →
      r ≤ ‖z - ((Real.pi : PhaseCircle) - t (otherEndpoint i e))‖) :
    let B := incidentEdges A i
    let B₁ := B.filter (fun e ↦ otherEndpoint i e ∈ G)
    let B₂ := B.filter (fun e ↦ otherEndpoint i e ∉ G)
    ‖degreeFourier A q d t‖ ≤
      Real.exp (-γ * B₁.card) * (Real.pi / r) ^ B₂.card *
        ‖degreeFourier A q d (Function.update t i z)‖ := by
  classical
  let B := incidentEdges A i
  let p := fun e ↦ otherEndpoint i e ∈ G
  let c (e : Edge α) : ℝ := if e ∈ B then (if p e then Real.exp (-γ) else Real.pi / r) else 1
  let s := Function.update t i z
  have hB : B ⊆ A := Finset.filter_subset _ _
  have hprod : (∏ e ∈ A, c e) =
      Real.exp (-γ * (B.filter p).card) * (Real.pi / r) ^ (B.filter fun e ↦ ¬p e).card := by
    have hb := Finset.prod_subset hB (f := c) (fun e _ he ↦ if_neg he)
    rw [← hb, ← Finset.prod_filter_mul_prod_filter_not B p c]
    have h₁ : (∏ e ∈ B.filter p, c e) = Real.exp (-γ) ^ (B.filter p).card := by
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro e he
      obtain ⟨heB, hep⟩ := Finset.mem_filter.mp he
      simp only [c, if_pos heB, if_pos hep]
    have h₂ : (∏ e ∈ B.filter (fun e ↦ ¬ p e), c e) =
        (Real.pi / r) ^ (B.filter fun e ↦ ¬ p e).card := by
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro e he
      obtain ⟨heB, hep⟩ := Finset.mem_filter.mp he
      simp only [c, if_pos heB, if_neg hep]
    rw [h₁, h₂, ← Real.exp_nat_mul, mul_comm (↑(B.filter p).card) (-γ)]
  have h := degreeFourier_norm_le_of_factor_comparison A q d t s c (fun e he ↦ by
    by_cases hb : e ∈ B
    · have hne := otherEndpoint_ne hb
      rw [incident_endpoint_sum hb t, incident_endpoint_sum hb s]
      change _ ≤ c e * ‖phaseBernoulliFactor (q e) (Function.update t i z i +
        Function.update t i z (otherEndpoint i e))‖
      rw [Function.update_self, Function.update_of_ne hne]
      by_cases hg : p e
      · simpa only [c, if_pos hb, if_pos hg] using
          hcompare e he (t i) (t (otherEndpoint i e)) z hx (hgood _ hg) hz
      · simp only [c, if_pos hb, if_neg hg]
        have hh : r ≤ ‖z + t (otherEndpoint i e) - (Real.pi : PhaseCircle)‖ := by
          have h' := havoid e hb hg
          rwa [show z - ((Real.pi : PhaseCircle) - t (otherEndpoint i e)) =
            z + t (otherEndpoint i e) - (Real.pi : PhaseCircle) by abel] at h'
        have hlow := (div_le_div_of_nonneg_right hh Real.pi_pos.le).trans
          (phaseBernoulliFactor_norm_ge_antipode (q e) (z + t (otherEndpoint i e)))
        have hpos : 0 < r / Real.pi := div_pos hr Real.pi_pos
        have hOne : 1 ≤ (Real.pi / r) * ‖phaseBernoulliFactor (q e) (z + t (otherEndpoint i e))‖ := by
          rw [mul_comm, ← inv_div, ← div_eq_mul_inv]
          exact (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hlow)
        have hnorm : ‖phaseBernoulliFactor (q e) (t i + t (otherEndpoint i e))‖ ≤ 1 := by
          have hq := (q e).property
          have hsq := phaseBernoulliFactor_norm_sq (q e) (t i + t (otherEndpoint i e))
          have hw : 0 ≤ (q e : ℝ) * (1 - q e) := mul_nonneg hq.1 (sub_nonneg.mpr hq.2)
          apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
          nlinarith only [hsq, mul_nonneg hw
            (sq_nonneg (Real.sin (‖t i + t (otherEndpoint i e)‖ / 2)))]
        exact hnorm.trans hOne
    · have hb' : ¬(e.val.1 = i ∨ e.val.2 = i) :=
        fun h ↦ hb (Finset.mem_filter.mpr ⟨he, h⟩)
      push_neg at hb'
      simp only [c, if_neg hb, one_mul, s, Function.update_of_ne hb'.1,
        Function.update_of_ne hb'.2, le_refl])
  rw [hprod] at h
  exact h

/-- Integrate the pointwise replacement estimate for a fixed mode, good
coordinate set and exceptional coordinate. -/
theorem integral_degreeFourier_exceptional_coordinate_le {n : ℕ}
    (A : Finset (Edge (Fin (n + 1)))) (G : Finset (Fin (n + 1)))
    (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (d : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) (b : PhaseCircle) {η γ r : ℝ}
    (hη : 0 < η) (hη' : η ≤ Real.pi) (hr : 0 < r) (hr' : r ≤ Real.pi)
    (hcompare : ∀ e ∈ A, ∀ x y w : PhaseCircle,
      10 * η ≤ ‖x - b‖ → ‖y - b‖ ≤ 3 * η → ‖w - b‖ ≤ η →
        ‖phaseBernoulliFactor (q e) (x + y)‖ ≤
          Real.exp (-γ) * ‖phaseBernoulliFactor (q e) (w + y)‖)
    (hpositive : 0 < η - (((incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∉ G)).card : ℝ) * r) :
    let B₁ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∈ G)
    let B₂ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∉ G)
    let f := fun t ↦ ‖degreeFourier A q d t‖
    let E := {t | (∀ j ∈ G, ‖t j - b‖ ≤ 3 * η) ∧ 10 * η ≤ ‖t i - b‖}
    (∫ t in E, f t ∂phaseLaw) ≤
      (Real.exp (-γ * B₁.card) * (Real.pi / r) ^ B₂.card / ((η - B₂.card * r) / Real.pi)) *
        ∫ t, f t ∂phaseLaw := by
  let B₁ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∈ G)
  let B₂ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∉ G)
  let f (t : Fin (n + 1) → PhaseCircle) := ‖degreeFourier A q d t‖
  let E := {t : Fin (n + 1) → PhaseCircle | (∀ j ∈ G, ‖t j - b‖ ≤ 3 * η) ∧ 10 * η ≤ ‖t i - b‖}
  let P := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ PhaseCircle) i).symm
  let μ : Measure PhaseCircle := AddCircle.haarAddCircle
  let ν : Measure (Fin n → PhaseCircle) := Measure.pi (fun _ ↦ μ)
  let c := Real.exp (-γ * B₁.card) * (Real.pi / r) ^ B₂.card
  let p := (η - B₂.card * r) / Real.pi
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hp : 0 < p := div_pos hpositive Real.pi_pos
  have hμ : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hν : IsProbabilityMeasure ν := by dsimp only [ν]; infer_instance
  have hP : MeasurePreserving P (μ.prod ν) phaseLaw :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) i).symm
  have hPdef (x : PhaseCircle) (y : Fin n → PhaseCircle) : P (x, y) = i.insertNth x y := rfl
  have heq (x w : PhaseCircle) (y : Fin n → PhaseCircle) :
      Function.update (P (x, y)) i w = P (w, y) := by
    apply funext
    apply (i.forall_iff_succAbove (P := fun j ↦ Function.update (P (x, y)) i w j = P (w, y) j)).mpr
    constructor
    · simp only [hPdef, Function.update_self, Fin.insertNth_apply_same]
    · intro k
      rw [Function.update_of_ne (Fin.succAbove_ne _ _)]
      simp only [hPdef, Fin.insertNth_apply_succAbove]
  have hE : MeasurableSet E := by
    rw [show E = (⋂ j ∈ G, {t : Fin (n + 1) → PhaseCircle | ‖t j - b‖ ≤ 3 * η}) ∩
      {t : Fin (n + 1) → PhaseCircle | 10 * η ≤ ‖t i - b‖} by ext t; simp [E]]
    exact (MeasurableSet.iInter (fun j ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_le (((measurable_pi_apply j).sub measurable_const).norm) measurable_const))).inter
      (measurableSet_le measurable_const (((measurable_pi_apply i).sub measurable_const).norm))
  have hint : Integrable f phaseLaw := (integrable_degreeFourier A q d).norm
  have h := integral_prod_region_le_of_replacement μ ν (f ∘ P)
    (hP.integrable_comp_of_integrable hint) (fun _ ↦ norm_nonneg _)
    (P ⁻¹' E) (P.measurable hE) hc hp
    (fun y ↦ by
      let centers (e : Edge (Fin (n + 1))) := (Real.pi : PhaseCircle) - P (0, y) (otherEndpoint i e)
      let Z := Metric.closedBall b η \ ⋃ e ∈ B₂, Metric.closedBall (centers e) r
      have hZ : MeasurableSet Z := MeasurableSet.diff measurableSet_closedBall
        (MeasurableSet.iUnion (fun e ↦ MeasurableSet.iUnion (fun _ ↦ measurableSet_closedBall)))
      refine ⟨Z, hZ, phase_replacement_measure_lower B₂ b centers hη.le hη' hr.le hr', ?_⟩
      intro x w hx hw
      change (∀ j ∈ G, ‖P (x, y) j - b‖ ≤ 3 * η) ∧ 10 * η ≤ ‖P (x, y) i - b‖ at hx
      have hx' : 10 * η ≤ ‖P (x, y) i - b‖ := hx.2
      have hw' : ‖w - b‖ ≤ η := by
        have hh := hw.1
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
      have havoid (e : Edge (Fin (n + 1))) (he : e ∈ incidentEdges A i)
          (he' : otherEndpoint i e ∉ G) :
          r ≤ ‖w - ((Real.pi : PhaseCircle) - P (x, y) (otherEndpoint i e))‖ := by
        have hu : P (0, y) (otherEndpoint i e) = P (x, y) (otherEndpoint i e) := by
          rw [← heq x 0 y, Function.update_of_ne (otherEndpoint_ne he)]
        have hn : w ∉ Metric.closedBall (centers e) r :=
          fun hh ↦ hw.2 (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨he, he'⟩, hh⟩⟩)
        have hh : r < ‖w - centers e‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hn
        simpa only [centers, hu] using hh.le
      have hstep := degreeFourier_exceptional_update_le A G q d (P (x, y)) i b w hr hx' hx.1 hw'
        hcompare havoid
      rw [heq] at hstep
      exact hstep)
  have hset : (∫ t in P ⁻¹' E, (f ∘ P) t ∂μ.prod ν) = ∫ t in E, f t ∂phaseLaw :=
    hP.setIntegral_preimage_emb P.measurableEmbedding f E
  have htotal : (∫ t, (f ∘ P) t ∂μ.prod ν) = ∫ t, f t ∂phaseLaw :=
    hP.integral_comp P.measurableEmbedding f
  rw [hset, htotal] at h
  exact h

end BoundedEdgeRegularSubgraphs
