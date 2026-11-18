module

public import BoundedEdgeRegularSubgraphs.CandidateMomentInputs
public import BoundedEdgeRegularSubgraphs.CandidateEnergy
public import BoundedEdgeRegularSubgraphs.InducedFreshBound
public import BoundedEdgeRegularSubgraphs.MeanSquareOverlapRates
public import BoundedEdgeRegularSubgraphs.OverlapSecondMoment
import Mathlib.Tactic

/-!
# Theorem 3.2: the mean-square imbalance lower bound
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The uniform formulation of Theorem 3.2, with a fixed threshold
on k²/N and the quadratic improvement at zero mean-square imbalance. -/
theorem eventually_exactOrder_failure_le_of_meanSquare {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ a₀ μ₀ c C : ℝ, 0 < a₀ ∧ 0 < μ₀ ∧ 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ N ≥ k, ∀ (q : Edge (Fin N) → Icc (0 : ℝ) 1) (p a η : ℝ),
        (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
        p ∈ Icc ξ (1 - ξ) → 0 ≤ a → a ≤ a₀ →
        let w := symmetricEdgeWeight (fun e ↦ (q e : ℝ))
        (∀ i, |sampleRowMean Finset.univ w i - p| ≤ a) →
        (∑ i, (sampleRowMean Finset.univ w i - p) ^ 2) ≤ (N : ℝ) * η ^ 2 →
        let μ := (k : ℝ) ^ 2 / N
        μ ≤ μ₀ → η ^ 2 * k ≤ c * Real.log ((N : ℝ) / (k : ℝ) ^ 2) →
        (graphLaw q).real (exactOrderEvent k)ᶜ ≤
          C * (if η = 0 then μ ^ 2 else μ ^ (3 / 2 : ℝ)) +
            C * Real.exp (-(k : ℝ) * Real.log k / 8) := by
  classical
  obtain ⟨δ, a₀, A, hδ, hδ₁, ha₀, hA, hCandidate⟩ := eventually_exists_candidate_family_local hξ hξ₁
  let ρ : ℝ := 3 / 4
  obtain ⟨C₁, D₁, hC₁, hD₁, hJoint⟩ := eventually_inducedDegreeAtom_sharedRatio_le
    hδ hδ₁ (ρ := ρ) (by norm_num [ρ]) (by norm_num [ρ])
  let D := D₁ + A / 2
  let μ₀ := min (1 / 2 : ℝ) ((1 / (2 * Real.exp D)) ^ (4 / 3 : ℝ))
  let c := min (1 / (4 * D)) (ρ / A)
  let b := 1 - Real.log ρ
  let C := 8 * C₁ * (Real.exp D) ^ 2 + 8
  have hρ : 0 < ρ := by norm_num [ρ]
  have hD : 0 < D := by dsimp only [D]; positivity
  have hμ₀ : 0 < μ₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨a₀, μ₀, c, C, ha₀, hμ₀, hc, hC, ?_⟩
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ Real.log k) atTop atTop := Real.tendsto_log_atTop.comp hcast
  filter_upwards [hCandidate, hJoint, eventually_ge_atTop (3 : ℕ),
    hlog.eventually_ge_atTop (8 * (A + ρ * b)),
    hcast.eventually_ge_atTop (2 * Real.exp 1 / ρ)] with k hF' hJ hk hLog hK
  intro N hN q p a η hq hp ha ha' w hDrift hEnergy μ hμ hTolerance
  let s : Finset (Fin N) := Finset.univ
  let H := Real.log ((N : ℝ) / (k : ℝ) ^ 2)
  let e := η ^ 2 * (k : ℝ)
  let B := (k : ℝ) * Real.log k / 2 + A * ((k : ℝ) + η ^ 2 * (k : ℝ) ^ 2)
  let g := Real.exp 1 * (k : ℝ) / (ρ * (N : ℝ))
  let t := ⌊ρ * (k : ℝ)⌋₊ + 1
  let W (j : ℕ) := if (j : ℝ) ≤ ρ * k then C₁ * Real.exp ((D + D * e) * (j : ℝ)) else Real.exp B
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hμ' : 0 < μ := div_pos (sq_pos_of_pos hk₀) hN₀
  have hμ₁ : μ ≤ 1 := hμ.trans ((min_le_left _ _).trans (by norm_num))
  have hH : H = -Real.log μ := by
    dsimp only [H, μ]
    rw [Real.log_div hN₀.ne' (sq_pos_of_pos hk₀).ne',
      Real.log_div (sq_pos_of_pos hk₀).ne' hN₀.ne']
    ring
  have hH₀ : 0 ≤ H := by rw [hH]; exact neg_nonneg.mpr (Real.log_nonpos hμ'.le hμ₁)
  have hDe : D * e ≤ -Real.log μ / 4 := by
    have he := hTolerance.trans (mul_le_mul_of_nonneg_right (min_le_left (1 / (4 * D)) (ρ / A)) hH₀)
    have h := mul_le_mul_of_nonneg_left he hD.le
    rwa [show D * (1 / (4 * D) * H) = H / 4 by field_simp [hD.ne'] <;> ring, hH] at h
  have hAe : A * e ≤ ρ * H := by
    have he := hTolerance.trans (mul_le_mul_of_nonneg_right (min_le_right (1 / (4 * D)) (ρ / A)) hH₀)
    have h := mul_le_mul_of_nonneg_left he hA.le
    rwa [show A * (ρ / A * H) = ρ * H by field_simp [hA.ne']] at h
  have hG : 0 < g := by dsimp only [g]; positivity
  have hG₁ : g ≤ 1 / 2 := by
    have hEq : g = Real.exp 1 * μ / (ρ * (k : ℝ)) := by
      dsimp only [g, μ]
      field_simp [hk₀.ne', hN₀.ne', hρ.ne'] <;> ring
    rw [hEq]
    apply (div_le_iff₀ (mul_pos hρ hk₀)).2
    have h := (div_le_iff₀ hρ).mp hK
    calc
      Real.exp 1 * μ ≤ Real.exp 1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ₁ (Real.exp_nonneg 1)
      _ ≤ (k : ℝ) * ρ / 2 := (le_div_iff₀ (by norm_num)).2 (by simpa only [mul_comm] using h)
      _ = _ := by ring
  have hGLog : Real.log g ≤ b - H - Real.log k := by
    apply Eq.le
    dsimp only [g, H, b]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (Real.exp_pos _).ne' hk₀.ne',
      Real.log_exp, Real.log_mul hρ.ne' hN₀.ne', Real.log_div hN₀.ne' (sq_pos_of_pos hk₀).ne',
      Real.log_pow]
    norm_num
    ring
  have hY : Real.exp D * μ ^ (3 / 4 : ℝ) ≤ 1 / 2 := by
    have hP := Real.rpow_le_rpow hμ'.le
      (hμ.trans (min_le_right (1 / 2 : ℝ) ((1 / (2 * Real.exp D)) ^ (4 / 3 : ℝ))))
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
    rw [← Real.rpow_mul (by positivity), show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, Real.rpow_one] at hP
    exact (mul_le_mul_of_nonneg_left hP (Real.exp_nonneg D)).trans_eq (by field_simp)
  obtain ⟨d, F, hEven, _, _, _, hHalf, hFam⟩ := hF' N hN q p a η hq hp ha ha' hDrift hEnergy
  have hS (S : Finset (Fin N)) (hS : S ∈ F) : S.card = k := (hFam S hS).1
  have hSubset : F ⊆ s.powersetCard k := by
    intro S hS'
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS S hS'⟩
  have hF₀ : F.Nonempty := by
    have hChoose : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hN
    exact Finset.card_pos.mp (Nat.cast_pos.mp ((show 0 < (N.choose k : ℝ) / 2 by positivity).trans_le hHalf))
  have hHalf' : s.card.choose k ≤ 2 * F.card := by
    have h : (N.choose k : ℝ) ≤ 2 * (F.card : ℝ) := by linarith only [hHalf]
    change (Finset.univ : Finset (Fin N)).card.choose k ≤ _
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast h
  let E (S : Finset (Fin N)) := inducedDegreeAtom S d
  have hpE (S : Finset (Fin N)) (hS : S ∈ F) : Real.exp (-B) ≤ (graphLaw q).real (E S) := by
    obtain ⟨_, θ, _, _, _, _, h⟩ := hFam S hS
    refine (Real.exp_le_exp.mpr ?_).trans h
    dsimp only [B]
    ring_nf
    exact le_rfl
  have hPositive (S : Finset (Fin N)) (hSF : S ∈ F) : 0 < (graphLaw q).real (E S) :=
    (Real.exp_pos _).trans_le (hpE S hSF)
  have hW₀ (j : ℕ) : 0 ≤ W j := by unfold W; split_ifs <;> positivity
  have hInd (S : Finset (Fin N)) (_ : S ∈ F) (T : Finset (Fin N)) (_ : T ∈ F)
      (hj : (S ∩ T).card ≤ 1) :
      (graphLaw q).real (E S ∩ E T) = (graphLaw q).real (E S) * (graphLaw q).real (E T) :=
    probability_inducedDegreeAtom_inter_of_small_overlap q S T d d hj
  have hRatio (S : Finset (Fin N)) (hSF : S ∈ F) (T : Finset (Fin N)) (hTF : T ∈ F)
      (_ : 2 ≤ (S ∩ T).card) :
      (graphLaw q).real (E S ∩ E T) / ((graphLaw q).real (E S) * (graphLaw q).real (E T)) ≤
        W (S ∩ T).card := by
    let J := S ∩ T
    let j := (J.card : ℝ)
    have hj₀ : 0 ≤ j := Nat.cast_nonneg _
    by_cases hj : j ≤ ρ * k
    · rw [show W (S ∩ T).card = C₁ * Real.exp ((D + D * e) * j) from ite_eq_left hj]
      obtain ⟨hS', θ, hdS, hδS, _, heS, _⟩ := hFam S hSF
      obtain ⟨hT', ψ, hdT, hδT, _, heT, _⟩ := hFam T hTF
      have h := hJ q (fun e ↦ ⟨hξ.trans_le (hq e).1, (hq e).2.trans_lt (by linarith only [hξ])⟩)
        S T hS' hT' θ ψ d hEven hδS hδT hdS hdT (hPositive S hSF) (hPositive T hTF) hj
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁.le)
      have hS₂ := (sum_extendCandidateTilt_sq_le S J θ Finset.inter_subset_left).trans heS
      have hT₂ := (sum_extendCandidateTilt_sq_le T J ψ Finset.inter_subset_right).trans heT
      have hC₂ := mul_le_mul_of_nonneg_left (add_le_add hS₂ hT₂) hj₀
      have hJk : j ≤ k := by
        change ((S ∩ T).card : ℝ) ≤ k
        exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := T))).trans hS'.le
      have hJ₂ : D₁ * j ^ 2 / (k : ℝ) ≤ D₁ * j := by
        apply (div_le_iff₀ hk₀).2
        nlinarith only [mul_le_mul_of_nonneg_left hJk (mul_nonneg hD₁.le hj₀)]
      dsimp only [D, e]
      nlinarith only [hJ₂, hC₂, mul_nonneg (mul_nonneg hD₁.le (mul_nonneg (sq_nonneg η) hk₀.le)) hj₀]
    · rw [show W (S ∩ T).card = Real.exp B from ite_eq_right hj]
      exact probability_inducedDegreeAtom_inter_div_mul_le_of_lower q S T d d B
        (hPositive S hSF) (hpE T hTF)
  have : IsProbabilityMeasure (graphLaw q) := by unfold graphLaw; infer_instance
  have hProb := (probability_exactOrder_failure_le_no_candidate q d F hS).trans
    (probability_no_candidate_le_overlap_sum (graphLaw q) s k F hSubset hF₀ hHalf' E
      (fun S _ ↦ measurableSet_inducedDegreeAtom S d) hPositive W hW₀ hInd hRatio)
  simp only [s, Finset.card_univ, Fintype.card_fin] at hProb
  let U := Finset.Icc 2 k
  let pOverlap (j : ℕ) := min (μ ^ j) ((Real.exp 1 * μ / j) ^ j)
  let Q := U.filter (fun j : ℕ ↦ (j : ℝ) ≤ ρ * k)
  let R := U.filter (fun j : ℕ ↦ ¬(j : ℝ) ≤ ρ * k)
  have hMod : (∑ j ∈ Q, pOverlap j * W j) ≤
      2 * C₁ * (Real.exp D) ^ 2 * (if η = 0 then μ ^ 2 else μ ^ (3 / 2 : ℝ)) := by
    have hb : (∑ j ∈ Q, pOverlap j * W j) ≤
        ∑ j ∈ U, μ ^ j * (C₁ * Real.exp ((D + D * e) * (j : ℝ))) := by
      calc
        _ ≤ ∑ j ∈ Q, μ ^ j * (C₁ * Real.exp ((D + D * e) * (j : ℝ))) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [show W j = C₁ * Real.exp ((D + D * e) * (j : ℝ)) from ite_eq_left (Finset.mem_filter.mp hj).2]
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
    by_cases hη : η = 0
    · rw [ite_eq_left hη]
      have he₀ : e = 0 := by simp [e, hη]
      have hsmall : μ * Real.exp D ≤ 1 / 2 := by
        have hh := Real.rpow_le_rpow_of_exponent_ge hμ' hμ₁ (show (3 / 4 : ℝ) ≤ 1 by norm_num)
        rw [Real.rpow_one] at hh
        exact (by rw [mul_comm μ]; exact mul_le_mul_of_nonneg_left hh (Real.exp_nonneg D) :
          μ * Real.exp D ≤ Real.exp D * μ ^ (3 / 4 : ℝ)).trans hY
      rw [he₀, mul_zero, add_zero] at hb
      exact hb.trans (moderate_overlap_sum_le_of_zero_imbalance hμ'.le hC₁.le k hsmall)
    · rw [ite_eq_right hη]
      exact hb.trans (moderate_overlap_sum_le_of_meanSquare hμ' hC₁.le hDe k hY)
  have hR : (∑ j ∈ R, pOverlap j * W j) ≤ 2 * Real.exp (-(k : ℝ) * Real.log k / 8) := by
    have ht : ρ * (k : ℝ) ≤ (t : ℝ) := by
      simpa only [t, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (ρ * (k : ℝ))).le
    have hSub : R ⊆ Finset.Icc t k := by
      intro j hj
      obtain ⟨hjU, hjR⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hjU).2⟩
      have hh : (⌊ρ * (k : ℝ)⌋₊ : ℝ) < j := (Nat.floor_le (by positivity)).trans_lt (lt_of_not_ge hjR)
      have hnat : ⌊ρ * (k : ℝ)⌋₊ < j := by exact_mod_cast hh
      exact Nat.succ_le_of_lt hnat
    have hb : (∑ j ∈ R, pOverlap j * W j) ≤ (∑ j ∈ Finset.Icc t k, g ^ j) * Real.exp B := by
      rw [Finset.sum_mul]
      refine (Finset.sum_le_sum ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun _ _ _ ↦ by positivity))
      intro j hj
      have hj' := lt_of_not_ge (Finset.mem_filter.mp hj).2
      rw [show W j = Real.exp B from ite_eq_right (Finset.mem_filter.mp hj).2]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      refine (min_le_right _ _).trans (pow_le_pow_left₀ (by positivity) ?_ _)
      have hh : Real.exp 1 * μ / (j : ℝ) ≤ Real.exp 1 * μ / (ρ * (k : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hρ hk₀) hj'.le
      exact hh.trans_eq (by dsimp only [μ, g]; field_simp [hk₀.ne', hN₀.ne', hρ.ne'] <;> ring)
    have hB : B = (k : ℝ) * Real.log k / 2 + A * ((k : ℝ) + e * k) := by dsimp only [B, e]; ring
    rw [hB] at hb
    exact hb.trans (large_overlap_sum_le_exp_of_meanSquare hG hG₁ ht hGLog hAe hLog)
  change _ ≤ 4 * ∑ j ∈ U, pOverlap j * W j at hProb
  have hSum := Finset.sum_filter_add_sum_filter_not U (fun j ↦ (j : ℝ) ≤ ρ * k)
    (fun j ↦ pOverlap j * W j)
  change (∑ j ∈ Q, pOverlap j * W j) + (∑ j ∈ R, pOverlap j * W j) =
    ∑ j ∈ U, pOverlap j * W j at hSum
  rw [← hSum] at hProb
  have h₁ : 0 ≤ (if η = 0 then μ ^ 2 else μ ^ (3 / 2 : ℝ)) := by split_ifs <;> positivity
  unfold C
  nlinarith only [hProb, hMod, hR, h₁, Real.exp_nonneg (-(k : ℝ) * Real.log k / 8),
    mul_nonneg (by positivity : 0 ≤ 8 * C₁ * (Real.exp D) ^ 2)
      (Real.exp_nonneg (-(k : ℝ) * Real.log k / 8))]

end BoundedEdgeRegularSubgraphs
