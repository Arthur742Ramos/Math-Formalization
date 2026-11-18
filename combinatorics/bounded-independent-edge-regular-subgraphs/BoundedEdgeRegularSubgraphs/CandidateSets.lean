module

public import BoundedEdgeRegularSubgraphs.CandidateDriftRates
public import BoundedEdgeRegularSubgraphs.CandidateRounding
public import BoundedEdgeRegularSubgraphs.InducedDegreeTargets
public import BoundedEdgeRegularSubgraphs.TiltedDegreeAtom
import Mathlib.Tactic

/-!
# Proposition 2.3: candidate sets
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- At least half of the samples have a tilt to the same integer degree,
with the norm and probability bounds from Proposition 2.3. -/
theorem eventually_exists_candidate_family {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ δ a₀ C : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < a₀ ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ N ≥ k, ∀ (q : Edge (Fin N) → Icc (0 : ℝ) 1) (p a η : ℝ),
        (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
        p ∈ Icc ξ (1 - ξ) → 0 ≤ a → a ≤ a₀ →
        let w := symmetricEdgeWeight (fun e ↦ (q e : ℝ))
        (∀ i, |sampleRowMean Finset.univ w i - p| ≤ a) →
        (∑ i, (sampleRowMean Finset.univ w i - p) ^ 2) ≤ (N : ℝ) * η ^ 2 →
        ∃ (d : ℤ) (F : Finset (Finset (Fin N))), Even ((k : ℤ) * d) ∧
          0 ≤ d ∧ d ≤ (k : ℤ) - 1 ∧ |(d : ℝ) - p * ((k : ℝ) - 1)| ≤ 1 ∧
          (N.choose k : ℝ) / 2 ≤ (F.card : ℝ) ∧
          ∀ S ∈ F, ∃ hS : S.card = k, ∃ θ : Fin k → ℝ,
            let f := S.orderIsoOfFin hS
            let qS := induce S q ∘ edgeEquiv f
            degreeSum (fun e ↦ (vertexTilt qS θ e : ℝ)) = (fun _ ↦ (d : ℝ)) ∧
            (∀ e, δ ≤ (vertexTilt qS θ e : ℝ) ∧ (vertexTilt qS θ e : ℝ) ≤ 1 - δ) ∧
            ‖θ‖ ≤ C * (a + candidateDriftRate k) ∧
            (∑ i, θ i ^ 2) ≤ C * (1 + η ^ 2 * k) ∧
            Real.exp (-(k : ℝ) / 2 * Real.log k - C * ((k : ℝ) + η ^ 2 * (k : ℝ) ^ 2)) ≤
              (graphLaw q).real (inducedDegreeAtom S d) := by
  classical
  obtain ⟨δ, ε, C₀, hδ, hδ₁, hε, hC₀, hTilt⟩ := eventually_vertexTilt_and_degreeAtom_lower hξ hξ₁
  let C := max (3 * C₀) (max (8 * C₀ ^ 2) (9 * C₀))
  have hC : 0 < C := (show 0 < 3 * C₀ by positivity).trans_le (le_max_left _ _)
  have hC₁ : 3 * C₀ ≤ C := le_max_left _ _
  have hC₂ : 8 * C₀ ^ 2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₃ : 9 * C₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ, ε / 2, C, hδ, hδ₁, by positivity, hC, ?_⟩
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hTilt, eventually_candidateDriftRates hε,
    hcast.eventually_ge_atTop (2 / ξ), eventually_ge_atTop (2 : ℕ)] with k hT hRate hK hk
  intro N hNk q p a η hq hp ha ha' w hα hη
  let m := ((k - 1 : ℕ) : ℝ)
  let z := candidateDriftRate k
  let s : Finset (Fin N) := Finset.univ
  let v := 2 * z
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hm : m = (k : ℝ) - 1 := by dsimp only [m]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hk₂ : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) < k := by linarith
  have hm₀ : 0 ≤ m := Nat.cast_nonneg _
  have hb : 1 ≤ ξ * m := by
    have h := (div_le_iff₀ hξ).mp hK
    have h' := mul_le_mul_of_nonneg_left (show (k : ℝ) / 2 ≤ m by linarith only [hm, hk₂]) hξ.le
    nlinarith only [h, h']
  have hp₀ : 1 ≤ p * ((k : ℝ) - 1) := by
    rw [← hm]
    exact hb.trans (mul_le_mul_of_nonneg_right hp.1 hm₀)
  have hp₁ : p * ((k : ℝ) - 1) ≤ (k : ℝ) - 2 := by
    have h := mul_le_mul_of_nonneg_right hp.2 hm₀
    rw [← hm]
    linarith only [h, hm, hb]
  obtain ⟨d, hEven, hd₀, hd₁, hd⟩ := exists_parity_rounded_degree k _ hp₀ hp₁
  have hd' : |p * m - (d : ℝ)| ≤ 1 := by rw [hm, abs_sub_comm]; exact hd
  have hw (i : Fin N) (_ : i ∈ s) (j : Fin N) (hj : j ∈ s.erase i) :
      w i j ∈ Icc (0 : ℝ) 1 := by
    have hne := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne hne.symm with hij | hji
    · rw [show w i j = (q ⟨(i, j), hij⟩ : ℝ) from symmetricEdgeWeight_eq_of_lt _ hij]
      exact (q _).property
    · rw [show w i j = (q ⟨(j, i), hji⟩ : ℝ) from symmetricEdgeWeight_eq_of_gt _ hji]
      exact (q _).property
  let F := (s.powersetCard k).filter (fun S ↦
    (∀ i ∈ S, |sampleRowDrift S w (d : ℝ) i| ≤ m * a + 1 + m * v) ∧
    (∑ i ∈ S, sampleRowDrift S w (d : ℝ) i ^ 2) ≤
      8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3)
  have hcard : (N.choose k : ℝ) / 2 ≤ (F.card : ℝ) := by
    have h := card_candidate_drift_bounds s w hk
      (by simpa only [s, Finset.card_univ, Fintype.card_fin] using hNk) p (d : ℝ) η
      (show 0 ≤ v by positivity) hw hd' (fun i _ ↦ hα i)
      (by simpa only [s, Finset.card_univ, Fintype.card_fin] using hη) hRate.1
    convert h using 1
    · simp only [s, Finset.card_univ, Fintype.card_fin]
    · congr 2
      ext S
      simp only [F, Finset.mem_filter, m]
  refine ⟨d, F, hEven, hd₀, hd₁, hd, hcard, fun S hS ↦ ?_⟩
  obtain ⟨hS', hSmax, hS₂⟩ := Finset.mem_filter.mp hS
  let hSord := (Finset.mem_powersetCard.mp hS').2
  let f := S.orderIsoOfFin hSord
  let qS := induce S q ∘ edgeEquiv f
  let r := degreeSum (fun e ↦ (qS e : ℝ)) - fun _ : Fin k ↦ (d : ℝ)
  have hDrift (i : Fin k) : r i = sampleRowDrift S w (d : ℝ) (f i).val := by
    change degreeSum ((induce S (fun e ↦ (q e : ℝ))) ∘ edgeEquiv f) i - (d : ℝ) = _
    rw [degreeSum_reindex f, degreeSum_induce_eq_sum_erase]
    rfl
  have hr : ‖r‖ ≤ (k : ℝ) * (a + 3 * z) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs, hDrift]
    exact (hSmax _ (f i).property).trans (hRate.2 a ha ha').1
  have hr' : ‖r‖ ≤ ε * (k : ℝ) := by
    refine hr.trans ?_
    rw [mul_comm (k : ℝ)]
    exact mul_le_mul_of_nonneg_right (hRate.2 a ha ha').2 hk₀.le
  have hr₂ : (∑ i, r i ^ 2) ≤ 8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3 := by
    simp_rw [hDrift]
    rw [show (∑ i : Fin k, sampleRowDrift S w (d : ℝ) (f i).val ^ 2) =
      ∑ i : S, sampleRowDrift S w (d : ℝ) i.val ^ 2 from
        f.toEquiv.sum_comp (fun i : S ↦ sampleRowDrift S w (d : ℝ) i.val ^ 2)]
    rw [← Finset.attach_eq_univ]
    exact (Finset.sum_attach S (fun i ↦ sampleRowDrift S w (d : ℝ) i ^ 2)).le.trans hS₂
  have hParity : Even (∑ _ : Fin k, d) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hEven
  obtain ⟨θ, hθ, hδq, hθsup, hθ₂, _, _, _, hAtom⟩ :=
    hT qS (fun _ ↦ d) (fun e ↦ hq (inducedEdge S (edgeEquiv f e))) hParity hr'
  refine ⟨hSord, θ, hθ, hδq, ?_, ?_, ?_⟩
  · refine hθsup.trans ?_
    apply (div_le_iff₀ hk₀).2
    have h := mul_le_mul_of_nonneg_left hr hC₀.le
    have h' := mul_le_mul_of_nonneg_right hC₁ (show 0 ≤ (a + z) * (k : ℝ) by positivity)
    have h₁ := mul_nonneg ha (show 0 ≤ C₀ * (k : ℝ) by positivity)
    nlinarith only [h, h', h₁]
  · refine hθ₂.trans ((mul_le_mul_of_nonneg_left hr₂ (sq_nonneg _)).trans ?_)
    have he : (C₀ / (k : ℝ)) ^ 2 * (8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3) =
        (8 * C₀ ^ 2) * (1 + η ^ 2 * k) := by field_simp [hk₀.ne'] <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hC₂ (by positivity)
  · have hTrans : (graphLaw qS).real (degreeAtom Finset.univ (fun _ ↦ d)) =
        (graphLaw q).real (inducedDegreeAtom S d) := by
      rw [probability_inducedDegreeAtom_eq]
      exact probability_degreeAtom_reindex f (induce S q) (fun _ ↦ d)
    rw [← hTrans]
    refine (Real.exp_le_exp.mpr ?_).trans hAtom
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr₂ hC₀.le) hk₀.le
    have h' : C₀ * (8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3) / k =
      8 * C₀ * (k + η ^ 2 * (k : ℝ) ^ 2) := by field_simp [hk₀.ne'] <;> ring
    rw [h'] at h
    have hC := mul_le_mul_of_nonneg_right hC₃
      (show 0 ≤ (k : ℝ) + η ^ 2 * (k : ℝ) ^ 2 by positivity)
    have hnonneg : 0 ≤ C₀ * (η ^ 2 * (k : ℝ) ^ 2) := by positivity
    nlinarith only [h, hC, hnonneg]

end BoundedEdgeRegularSubgraphs
