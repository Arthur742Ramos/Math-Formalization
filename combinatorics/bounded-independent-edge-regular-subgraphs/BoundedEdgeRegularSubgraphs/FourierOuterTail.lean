module

public import BoundedEdgeRegularSubgraphs.FourierExceptionalCover
public import BoundedEdgeRegularSubgraphs.FourierExceptionalCoordinate
public import BoundedEdgeRegularSubgraphs.FourierPhaseAnnulus
import Mathlib.Tactic

/-!
# The integral outside the two fixed phase boxes
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The finite form of (B.1), with the factor for each choice of exceptional
coordinate and with the number of choices displayed. -/
theorem integral_degreeFourier_outside_fixed_boxes_le {n : ℕ}
    (S : Finset (Fin (n + 1))) (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (d : Fin (n + 1) → ℤ)
    (m L : ℕ) {η lower γ r : ℝ} (hη : 0 < η) (hηπ : η ≤ Real.pi) (hlower : 0 ≤ lower)
    (hγ : 0 ≤ γ) (hr : 0 < r) (hrπ : r ≤ Real.pi) (hwindow : 0 < η - L * r)
    (hq : ∀ e, lower ≤ (q e : ℝ) * (1 - q e))
    (hdeg : 2 * m ≤ ((Finset.univ : Finset (Fin (n + 1))) \ S).card * L)
    (hpair : let t := ((Finset.univ : Finset (Fin (n + 1))) \ S).card - (L + 1)
      2 * m < t * (t - 1))
    (hcomp : ∀ e : Edge (Fin (n + 1)), ∀ x y w b : PhaseCircle,
      (b = 0 ∨ b = (Real.pi : PhaseCircle)) →
      10 * η ≤ ‖x - b‖ → ‖y - b‖ ≤ 3 * η → ‖w - b‖ ≤ η →
        ‖phaseBernoulliFactor (q e) (x + y)‖ ≤ Real.exp (-γ) * ‖phaseBernoulliFactor (q e) (w + y)‖) :
    let A := edgesOutsideOverlap S
    let g := (n + 1) - S.card - L
    let f := fun t ↦ ‖degreeFourier A q d t‖
    let c := Real.exp (-γ * g) * (Real.pi / r) ^ L / ((η - L * r) / Real.pi)
    (∫ t in (phaseBox 0 (10 * η) ∪ phaseBox (Real.pi : PhaseCircle) (10 * η))ᶜ, f t ∂phaseLaw) ≤
      Real.exp (-(2 * lower * Real.sin (η / 2) ^ 2) * m) +
        (2 * (n + 1) * ((n + 1).choose ((n + 1) - L)) : ℕ) * c * ∫ t, f t ∂phaseLaw := by
  classical
  let k := n + 1
  let A := edgesOutsideOverlap S
  let f (t : Fin k → PhaseCircle) := ‖degreeFourier A q d t‖
  let J := ∫ t, f t ∂phaseLaw
  let g := k - S.card - L
  let c := Real.exp (-γ * g) * (Real.pi / r) ^ L / ((η - L * r) / Real.pi)
  let v (b : Bool) : PhaseCircle := if b then (Real.pi : PhaseCircle) else 0
  let R := (Finset.univ : Finset (Fin k)).powersetCard (k - L)
  let K := Bool × R × Fin k
  let E (a : K) := {t : Fin k → PhaseCircle |
    (∀ j ∈ a.2.1.val, ‖t j - v a.1‖ ≤ 3 * η) ∧ 10 * η ≤ ‖t a.2.2 - v a.1‖}
  let M := {t : Fin k → PhaseCircle | m ≤ (A.filter fun e ↦ η < ‖t e.val.1 + t e.val.2‖).card}
  let O : Set (Fin k → PhaseCircle) :=
    (phaseBox (0 : PhaseCircle) (10 * η) ∪ phaseBox (Real.pi : PhaseCircle) (10 * η))ᶜ
  have hf : Integrable f phaseLaw := (integrable_degreeFourier A q d).norm
  have h₀ (t : Fin k → PhaseCircle) : 0 ≤ f t := norm_nonneg _
  have hJ : 0 ≤ J := integral_nonneg h₀
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hb (b : Bool) : v b = 0 ∨ v b = (Real.pi : PhaseCircle) := by cases b <;> simp [v]
  have hE (a : K) : MeasurableSet (E a) := by
    rw [show E a = (⋂ j ∈ a.2.1.val, {t : Fin k → PhaseCircle | ‖t j - v a.1‖ ≤ 3 * η}) ∩
      {t : Fin k → PhaseCircle | 10 * η ≤ ‖t a.2.2 - v a.1‖} by ext t; simp [E]]
    exact (MeasurableSet.iInter (fun j ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_le (((measurable_pi_apply j).sub measurable_const).norm) measurable_const))).inter
      (measurableSet_le measurable_const (((measurable_pi_apply a.2.2).sub measurable_const).norm))
  have hcover : O ⊆ M ∪ ⋃ a, E a := by
    intro t ht
    by_cases hm : t ∈ M
    · exact Or.inl hm
    · have hbad : (A.filter fun e ↦ η < ‖t e.val.1 + t e.val.2‖).card ≤ m :=
        (lt_of_not_ge hm).le
      obtain ⟨b, G, i, hb', hG, _, hnear, hfar⟩ :=
        exists_exceptional_phase_coordinate S t hη m L hdeg hpair hbad ht
      let G' : R := ⟨G, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
        by simpa only [Fintype.card_fin, k] using hG⟩⟩
      right
      apply mem_iUnion.mpr
      rcases hb' with rfl | rfl
      · refine ⟨(false, G', i), ?_⟩
        simpa [E, v, G'] using And.intro hnear hfar.le
      · refine ⟨(true, G', i), ?_⟩
        simpa [E, v, G'] using And.intro hnear hfar.le
  have hpiece (a : K) : (∫ t in E a, f t ∂phaseLaw) ≤ c * J := by
    let G := a.2.1.val
    let i := a.2.2
    have hG : G.card = k - L := (Finset.mem_powersetCard.mp a.2.1.property).2
    by_cases hi : i ∈ G
    · have he : E a = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        change (∀ j ∈ G, ‖t j - v a.1‖ ≤ 3 * η) ∧ 10 * η ≤ ‖t i - v a.1‖ at ht
        linarith only [ht.1 i hi, ht.2, hη]
      rw [he, setIntegral_empty]
      exact mul_nonneg hc hJ
    · let B₁ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∈ G)
      let B₂ := (incidentEdges A i).filter (fun e ↦ otherEndpoint i e ∉ G)
      have hgood : g ≤ B₁.card := by
        have hh := good_incidentEdges_card_ge S G hi
        have hs := Finset.le_card_sdiff S G
        have hg₀ : g = G.card - S.card := by rw [hG]; dsimp only [g]; omega
        rw [hg₀]
        exact hs.trans hh
      have hbad : B₂.card ≤ L := by
        have hl := exceptional_incidentEdges_card_le A G i
        have hgc : (((Finset.univ : Finset (Fin k)) \ G).erase i).card ≤ L := by
          refine Finset.card_erase_le.trans ?_
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ G), Finset.card_univ,
            Fintype.card_fin, hG]
          omega
        exact hl.trans hgc
      have hwindows : 0 < η - (B₂.card : ℝ) * r := by
        have h := mul_le_mul_of_nonneg_right (show (B₂.card : ℝ) ≤ L by exact_mod_cast hbad) hr.le
        linarith only [hwindow, h]
      have h := integral_degreeFourier_exceptional_coordinate_le A G q d i (v a.1)
        hη hηπ hr hrπ (fun e _ x y w ↦ hcomp e x y w (v a.1) (hb a.1)) hwindows
      have h₁ : Real.exp (-γ * B₁.card) ≤ Real.exp (-γ * g) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by exact_mod_cast hgood) (neg_nonpos.mpr hγ))
      have h₂ : (Real.pi / r) ^ B₂.card ≤ (Real.pi / r) ^ L :=
        pow_le_pow_right₀ ((one_le_div₀ hr).mpr hrπ) hbad
      have h₃ : (η - L * r) / Real.pi ≤ (η - B₂.card * r) / Real.pi := by
        apply div_le_div_of_nonneg_right _ Real.pi_pos.le
        exact sub_le_sub_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) hr.le) _
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hJ)
      exact div_le_div₀ (by positivity) (mul_le_mul h₁ h₂ (by positivity) (by positivity))
        (div_pos hwindow Real.pi_pos) h₃
  have hU : (∫ t in ⋃ a, E a, f t ∂phaseLaw) ≤ (Fintype.card K : ℝ) * c * J := by
    calc
      _ ≤ ∑ a, ∫ t in E a, f t ∂phaseLaw := setIntegral_iUnion_le_of_nonneg hf h₀ E hE
      _ ≤ ∑ _ : K, c * J := Finset.sum_le_sum (fun a _ ↦ hpiece a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  let U := ⋃ a, E a
  have hsum : (∫ t in M ∪ U, f t ∂phaseLaw) ≤
      (∫ t in M, f t ∂phaseLaw) + ∫ t in U, f t ∂phaseLaw := by
    have hM : Integrable f (phaseLaw.restrict M) := hf.integrableOn
    have hU : Integrable f (phaseLaw.restrict U) := hf.integrableOn
    have h := integral_mono_measure (Measure.restrict_union_le (μ := phaseLaw) M U)
      (ae_of_all _ h₀) (hM.add_measure hU)
    rwa [integral_add_measure hM hU] at h
  have hK : Fintype.card K = 2 * k * (k.choose (k - L)) := by
    change Fintype.card (Bool × ↥R × Fin k) = _
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]
    have hR : R.card = k.choose (k - L) := by
      dsimp only [R]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hR]
    ac_rfl
  calc
    _ ≤ ∫ t in M ∪ U, f t ∂phaseLaw :=
      setIntegral_mono_set hf.integrableOn (ae_of_all _ h₀) (ae_of_all _ hcover)
    _ ≤ (∫ t in M, f t ∂phaseLaw) + ∫ t in U, f t ∂phaseLaw := hsum
    _ ≤ _ := by
      rw [hK] at hU
      exact add_le_add
        (integral_degreeFourier_many_bad_le A q d m hη.le hlower (fun e _ ↦ hq e)) hU

end BoundedEdgeRegularSubgraphs
