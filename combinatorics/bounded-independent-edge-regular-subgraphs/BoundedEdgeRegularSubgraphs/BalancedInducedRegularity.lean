module

public import BoundedEdgeRegularSubgraphs.CandidateMomentInputs
public import BoundedEdgeRegularSubgraphs.CandidateEnergy
public import BoundedEdgeRegularSubgraphs.InducedFreshBound
public import BoundedEdgeRegularSubgraphs.BalancedOverlapAverage
public import BoundedEdgeRegularSubgraphs.BalancedOverlapRates
public import BoundedEdgeRegularSubgraphs.BalancedLargeOverlap
public import BoundedEdgeRegularSubgraphs.SupportedSecondMoment
import Mathlib.Tactic

/-!
# Positive probability for nearly equal expected degrees
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

set_option maxHeartbeats 650000 in
/-- Theorem 4.1, including the common fixed-degree target of the
successful candidates. -/
theorem eventually_fixedDegree_success_of_nearBalance {ξ M : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hM : 0 ≤ M) :
    ∃ L p₀ : ℝ, 1 ≤ L ∧ 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ N : ℕ, L * (k : ℝ) * Real.sqrt k ≤ N →
        ∀ (q : Edge (Fin N) → Icc (0 : ℝ) 1) (p : ℝ),
          (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) → p ∈ Icc ξ (1 - ξ) →
          (∀ i, |sampleRowMean Finset.univ (symmetricEdgeWeight (fun e ↦ (q e : ℝ))) i - p| ≤
            Real.sqrt (M / k)) →
          ∃ (d : ℤ) (F : Finset (Finset (Fin N))), Even ((k : ℤ) * d) ∧
            0 ≤ d ∧ d ≤ (k : ℤ) - 1 ∧ |(d : ℝ) - p * ((k : ℝ) - 1)| ≤ 1 ∧
            (∀ S ∈ F, S.card = k) ∧
            p₀ ≤ (graphLaw q).real (⋃ S ∈ F, inducedDegreeAtom S d) := by
  classical
  obtain ⟨δ, a₀, C, hδ, hδ₁, ha₀, hC, hCandidate⟩ := eventually_exists_candidate_family_local hξ hξ₁
  let ρ : ℝ := 3 / 4
  obtain ⟨B₀, D, hB₀, hD, hJoint⟩ := eventually_inducedDegreeAtom_sharedRatio_le
    hδ hδ₁ (ρ := ρ) (by norm_num [ρ]) (by norm_num [ρ])
  obtain ⟨C₀, hC₀, hFresh⟩ := probability_inducedDegreeAtom_inter_le_fresh_edges.{0} hξ hξ₁
  let A := 1 + C * (1 + M) + 2 * C ^ 2 * (M + 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAC : C * (1 + M) ≤ A := by dsimp only [A]; linarith only [mul_nonneg (sq_nonneg C) (show 0 ≤ M + 1 by positivity)]
  have hAC' : 2 * C ^ 2 * (M + 1) ≤ A := by dsimp only [A]; linarith only [mul_nonneg hC.le (show 0 ≤ 1 + M by positivity)]
  obtain ⟨L, hL, hLarge⟩ := balanced_overlap_fresh_product_le_exp hA.le hC₀
  obtain ⟨Q, hQ, hScalar⟩ := eventually_balanced_overlap_weight_sum_le hA
    (show 0 < D + A by positivity) (show 0 ≤ D + A / 2 by positivity)
  let B₁ := max 1 B₀
  let K := 2 * B₁ * Q
  have hB₁ : 1 ≤ B₁ := le_max_left _ _
  have hK : 0 < K := by dsimp only [K]; positivity
  have hK₁ : 1 ≤ K := by
    dsimp only [K]
    nlinarith only [hQ, hB₁, mul_nonneg (sub_nonneg.mpr hB₁) (sub_nonneg.mpr hQ)]
  refine ⟨L, K⁻¹, hL, inv_pos.mpr hK, inv_le_one_of_one_le₀ hK₁, ?_⟩
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ Real.log k) atTop atTop := Real.tendsto_log_atTop.comp hcast
  filter_upwards [hCandidate, hJoint, hScalar, eventually_ge_atTop (4 : ℕ),
    hcast.eventually_ge_atTop (M / a₀ ^ 2), hlog.eventually_ge_atTop 1] with k hCan hJ hSc hk hkM hLog
  intro N hN q p hq hp hDrift
  let a := Real.sqrt (M / k)
  let s : Finset (Fin N) := Finset.univ
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkS : 1 ≤ Real.sqrt k := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega))
  have hN' : k ≤ N := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hL hk₀.le) hkS (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ L * (k : ℝ))
    exact_mod_cast (by simpa only [one_mul, mul_one] using hh.trans hN : (k : ℝ) ≤ N)
  have hN₀ : (0 : ℝ) < N := hk₀.trans_le (by exact_mod_cast hN')
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha₂ : a ^ 2 = M / k := Real.sq_sqrt (by positivity)
  have ha' : a ≤ a₀ := Real.sqrt_le_iff.mpr ⟨ha₀.le,
    (div_le_iff₀ hk₀).2 ((div_le_iff₀ (sq_pos_of_pos ha₀)).1 hkM |>.trans_eq (mul_comm _ _))⟩
  have hMS : (∑ i : Fin N,
      (sampleRowMean Finset.univ (symmetricEdgeWeight (fun e ↦ (q e : ℝ))) i - p) ^ 2) ≤
        (N : ℝ) * a ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin N, a ^ 2 := Finset.sum_le_sum (fun i _ ↦ by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hDrift i) _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨d, F, hEven, hd₀, hd₁, hd, hHalf, hFam⟩ :=
    hCan N hN' q p a a hq hp ha ha' hDrift hMS
  let θ (S : Finset (Fin N)) : S → ℝ := if h : S ∈ F then Classical.choose (hFam S h).2 else 0
  let u (S : Finset (Fin N)) := extendCandidateTilt S (θ S)
  let B := (k : ℝ) * Real.log k / 2 + A * k
  let μ := (k : ℝ) ^ 2 / N
  let P := overlapMass N k
  let t := (k : ℝ) / (A * Real.log k)
  let W (j : ℕ) := if (j : ℝ) ≤ t then P j * Real.exp ((D + A) * (j : ℝ) ^ 2 / k)
    else if (j : ℝ) ≤ ρ * k then P j * Real.exp ((D + A / 2) * (j : ℝ))
    else Real.exp (-(k : ℝ))
  have hS (S : Finset (Fin N)) (hS : S ∈ F) : S.card = k := (hFam S hS).1
  have hSubset : F ⊆ s.powersetCard k := fun S h ↦ Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS S h⟩
  have hChoose : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hN'
  have hF₀ : F.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((by positivity : 0 < (N.choose k : ℝ)/2).trans_le hHalf))
  have hf : 0 < (F.card : ℝ) := Nat.cast_pos.mpr hF₀.card_pos
  have hCard : s.card = N := by simp [s]
  obtain ⟨S₀, hS₀⟩ := hF₀
  have hUP : (∑ j ∈ Finset.range (k + 1), P j) = 1 := by
    simpa only [P, hCard] using sum_overlapMass_eq_one s S₀ (Finset.subset_univ _) (hS S₀ hS₀)
  have hPow (j : ℕ) (hj : 0 < j) (hjk : j ≤ k) : P j ≤ (Real.exp 1 * μ / j) ^ j := by
    simpa only [P, μ, hCard] using overlapMass_le_pow s S₀ (Finset.subset_univ _) (hS S₀ hS₀) hj hjk
  have hμ : μ ≤ Real.sqrt k := by
    apply (div_le_iff₀ hN₀).2
    have h := mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg k)
    have hh := Real.sq_sqrt hk₀.le
    have h₁ : Real.sqrt k * (L * (k : ℝ) * Real.sqrt k) = L * (k : ℝ) ^ 2 := by
      calc
        _ = L * (k : ℝ) * (Real.sqrt k ^ 2) := by ring
        _ = _ := by rw [hh]; ring
    rw [h₁] at h
    exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (sq_nonneg (k : ℝ)) :
      (k : ℝ) ^ 2 ≤ L * (k : ℝ) ^ 2).trans h
  obtain ⟨htρ, hW⟩ := hSc μ (by positivity) hμ P (overlapMass_nonneg N k) hUP hPow
  have hW₀ (j : ℕ) : 0 ≤ W j := by unfold W; split_ifs <;> first | positivity | exact mul_nonneg (overlapMass_nonneg _ _ _) (Real.exp_nonneg _)
  have hFits (S : Finset (Fin N)) (hSF : S ∈ F) := Classical.choose_spec (hFam S hSF).2
  have hFit (S : Finset (Fin N)) (hSF : S ∈ F) : θ S = Classical.choose (hFam S hSF).2 := dif_pos hSF
  let E (S : Finset (Fin N)) := inducedDegreeAtom S d
  let ν := graphLaw q
  have : IsProbabilityMeasure ν := by unfold ν graphLaw; infer_instance
  have hEnergy (S : Finset (Fin N)) (hSF : S ∈ F) : (∑ i ∈ S, u S i ^ 2) ≤ A := by
    rw [show u S = extendCandidateTilt S (θ S) by rfl, sum_extendCandidateTilt_sq_eq, hFit S hSF]
    have h := (hFits S hSF).2.2.2.1
    refine h.trans ?_
    rw [ha₂, div_mul_cancel₀ _ hk₀.ne']
    exact hAC
  have hPoint (S : Finset (Fin N)) (hSF : S ∈ F) (i : Fin N) (hi : i ∈ S) :
      u S i ^ 2 ≤ A * Real.log k / (k : ℝ) := by
    have ht : |u S i| ≤ C * (a + candidateDriftRate k) := by
      rw [show u S = extendCandidateTilt S (θ S) by rfl, extendCandidateTilt_eq_of_mem S _ hi, hFit S hSF]
      exact (hFits S hSF).2.2.1 ⟨i, hi⟩
    have h := pow_le_pow_left₀ (abs_nonneg _) ht 2
    rw [sq_abs, mul_pow] at h
    have hR : (candidateDriftRate k) ^ 2 = Real.log k / (k : ℝ) := Real.sq_sqrt (by positivity)
    have hn := sq_nonneg (a - candidateDriftRate k)
    have hAdd : (a + candidateDriftRate k) ^ 2 ≤ 2 * ((M + 1) * Real.log k / (k : ℝ)) := by
      have hM' := mul_le_mul_of_nonneg_left hLog hM
      have hMk := div_le_div_of_nonneg_right hM' hk₀.le
      rw [mul_one] at hMk
      have hEq : (M + 1) * Real.log k / (k : ℝ) = M * Real.log k / (k : ℝ) + Real.log k / (k : ℝ) := by ring
      rw [hEq]
      nlinarith only [hn, ha₂, hR, hMk]
    refine h.trans ((mul_le_mul_of_nonneg_left hAdd (sq_nonneg C)).trans ?_)
    have h := mul_le_mul_of_nonneg_right hAC' (show 0 ≤ Real.log k / (k : ℝ) by positivity)
    convert h using 1 <;> ring
  have hProb (S : Finset (Fin N)) (hSF : S ∈ F) : Real.exp (-B) ≤ ν.real (E S) := by
    refine (Real.exp_le_exp.mpr ?_).trans (hFits S hSF).2.2.2.2
    have h := mul_le_mul_of_nonneg_right hAC hk₀.le
    have hEq : a ^ 2 * (k : ℝ) ^ 2 = M * (k : ℝ) := by rw [ha₂]; field_simp
    rw [hEq]
    dsimp only [B]
    nlinarith only [h]
  have hPos (S : Finset (Fin N)) (hSF : S ∈ F) : 0 < ν.real (E S) :=
    (Real.exp_pos _).trans_le (hProb S hSF)
  let R (S T : Finset (Fin N)) := ν.real (E S ∩ E T) / (ν.real (E S) * ν.real (E T))
  have hRsmall (S : Finset (Fin N)) (hSF : S ∈ F) (T : Finset (Fin N)) (hTF : T ∈ F)
      (hj : ((S ∩ T).card : ℝ) ≤ ρ * k) :
      R S T ≤ B₀ * Real.exp (D * ((S ∩ T).card : ℝ) ^ 2 / k + ((S ∩ T).card : ℝ) / 4 *
        ((∑ i ∈ S ∩ T, u S i ^ 2) + (∑ i ∈ S ∩ T, u T i ^ 2))) := by
    have hs := hFits S hSF
    have ht := hFits T hTF
    rw [← hFit S hSF] at hs
    rw [← hFit T hTF] at ht
    refine (hJ q (fun e ↦ ⟨hξ.trans_le (hq e).1, (hq e).2.trans_lt (by linarith only [hξ])⟩)
      S T (hS S hSF) (hS T hTF) (θ S) (θ T) d hEven hs.2.1 ht.2.1 hs.1 ht.1 (hPos S hSF) (hPos T hTF) hj).trans_eq ?_
    dsimp only [u]
    congr 1
    ring
  have hRlarge (S : Finset (Fin N)) (hSF : S ∈ F) (T : Finset (Fin N)) (hTF : T ∈ F) :
      R S T ≤ Real.exp B * ((C₀ / Real.sqrt ((k - (S ∩ T).card : ℕ) + 1)) ^ (S ∩ T).card) := by
    have hh := hFresh q hq S T d d
    rw [hS T hTF] at hh
    have h := mul_le_mul_of_nonneg_left (hProb T hTF) (Real.exp_nonneg B)
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    apply (div_le_iff₀ (mul_pos (hPos S hSF) (hPos T hTF))).2
    refine hh.trans ?_
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤
      ((C₀ / Real.sqrt ((k - (S ∩ T).card : ℕ) + 1)) ^ (S ∩ T).card) * ν.real (E S) by
        exact mul_nonneg (by positivity) measureReal_nonneg)
    nlinarith only [h']
  let m : ℝ := F.card
  let V : ℝ := N.choose k
  have hCV (j : ℕ) : ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) = V * P j := by
    dsimp only [P, overlapMass, V]
    rw [hCard, mul_comm (N.choose k : ℝ), div_mul_cancel₀ _ hChoose.ne']
  have hFull (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      (∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then R S T else 0) ≤ m * V * B₁ * W j := by
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    by_cases hs : (j : ℝ) ≤ t
    · rw [show W j = P j * Real.exp ((D + A) * (j : ℝ) ^ 2 / k) from ite_eq_left hs]
      let b := B₀ * Real.exp (D * (j : ℝ) ^ 2 / k)
      have hb : 0 ≤ b := by dsimp only [b]; positivity
      let G (S T : Finset (Fin N)) := Real.exp ((j : ℝ) / 4 *
        ((∑ i ∈ S ∩ T, u S i ^ 2) + (∑ i ∈ S ∩ T, u T i ^ 2)))
      have hsm (S : Finset (Fin N)) (hSF : S ∈ F) (i : Fin N) (hi : i ∈ S) :
          (j : ℝ) * u S i ^ 2 ≤ 1 := by
        have hLog₀ : 0 < A * Real.log k := by positivity
        have h := (le_div_iff₀ hLog₀).1 hs
        have hh := mul_le_mul_of_nonneg_left (hPoint S hSF i hi) hj₀
        refine hh.trans ?_
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hk₀).2 (by simpa only [one_mul] using h)
      calc
        _ ≤ ∑ S ∈ F, ∑ T ∈ F, b * (if (S ∩ T).card = j then G S T else 0) := by
          apply Finset.sum_le_sum
          intro S hSF
          apply Finset.sum_le_sum
          intro T hTF
          split_ifs with h
          · have hj' : ((S ∩ T).card : ℝ) ≤ ρ * k := by rw [h]; exact hs.trans htρ
            have h := hRsmall S hSF T hTF hj'
            rw [‹(S ∩ T).card = j›, Real.exp_add] at h
            exact h.trans_eq (by dsimp only [b, G]; ring)
          · rw [mul_zero]
        _ ≤ b * ((F.card : ℝ) * ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) *
            Real.exp (A * (j : ℝ) ^ 2 / k)) := by
          simp_rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_balanced_overlap_exp_le s k j (by omega) hjk F hSubset u hA.le hEnergy hsm) hb
        _ ≤ _ := by
          have h' := hCV j
          have hrew : b * ((F.card : ℝ) * ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) *
              Real.exp (A * (j : ℝ) ^ 2 / k)) =
                m * V * B₀ * (P j * Real.exp ((D + A) * (j : ℝ) ^ 2 / k)) := by
            rw [show (D + A) * (j : ℝ) ^ 2 / k = D * (j : ℝ) ^ 2 / k + A * (j : ℝ) ^ 2 / k by ring,
              Real.exp_add, mul_assoc (F.card : ℝ) (((s.card - k).choose (k - j) : ℝ))
                (k.choose j : ℝ), h']
            dsimp only [m, b]
            ring
          rw [hrew]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right _ _) (by dsimp only [m, V]; positivity))
            (mul_nonneg (overlapMass_nonneg _ _ _) (Real.exp_nonneg _))
    · by_cases hm : (j : ℝ) ≤ ρ * k
      · rw [show W j = P j * Real.exp ((D + A / 2) * (j : ℝ)) by dsimp only [W]; rw [ite_eq_right hs, ite_eq_left hm]]
        have hband := sum_overlapBand_le_of_pointwise s F hSubset hjk R
          (B := B₀ * Real.exp ((D + A / 2) * (j : ℝ))) (by positivity) (by
            intro S hSF T hTF h
            have hj' : ((S ∩ T).card : ℝ) ≤ ρ * k := by rw [h]; exact hm
            refine (hRsmall S hSF T hTF hj').trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB₀.le)
            rw [h]
            have h₁ : (∑ i ∈ S ∩ T, u S i ^ 2) ≤ A :=
              (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
                (fun _ _ _ ↦ sq_nonneg _)).trans (hEnergy S hSF)
            have h₂ : (∑ i ∈ S ∩ T, u T i ^ 2) ≤ A :=
              (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
                (fun _ _ _ ↦ sq_nonneg _)).trans (hEnergy T hTF)
            have hJ : (j : ℝ) ≤ k := by exact_mod_cast hjk
            have hD' : D * (j : ℝ) ^ 2 / k ≤ D * (j : ℝ) :=
              (div_le_iff₀ hk₀).2 (by nlinarith only [mul_le_mul_of_nonneg_left hJ (mul_nonneg hD.le hj₀)])
            nlinarith only [hD', mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (show 0 ≤ (j : ℝ) / 4 by positivity)])
        rw [hCV] at hband
        refine hband.trans ?_
        have hb := mul_le_mul_of_nonneg_left (le_max_right 1 B₀) (show 0 ≤ m * V * P j by
          exact mul_nonneg (by dsimp only [m, V]; positivity) (overlapMass_nonneg _ _ _))
        have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg ((D + A / 2) * (j : ℝ)))
        nlinarith only [hb']
      · rw [show W j = Real.exp (-(k : ℝ)) by dsimp only [W]; rw [ite_eq_right hs, ite_eq_right hm]]
        let f := (C₀ / Real.sqrt ((k - j : ℕ) + 1)) ^ j
        have hband := sum_overlapBand_le_of_pointwise s F hSubset hjk R
          (B := Real.exp B * f) (by dsimp only [f]; positivity) (by
            intro S hSF T hTF h
            simpa only [f, h] using hRlarge S hSF T hTF)
        have hjρ : (3 / 4 : ℝ) * (k : ℝ) ≤ (j : ℝ) := (lt_of_not_ge hm).le
        have hpScale : P j ≤ (Real.exp 1 * (k : ℝ) / ((3 / 4 : ℝ) * N)) ^ j := by
          have hj₀' : (0 : ℝ) < j := (by positivity : 0 < (3 / 4 : ℝ) * (k : ℝ)).trans_le hjρ
          refine (hPow j (by exact_mod_cast hj₀') hjk).trans (pow_le_pow_left₀ (by positivity) ?_ _)
          refine (div_le_div_of_nonneg_left (by positivity : 0 ≤ Real.exp 1 * μ)
            (by positivity : 0 < (3 / 4 : ℝ) * (k : ℝ)) hjρ).trans_eq ?_
          dsimp only [μ]
          field_simp
        have hProduct := hLarge hk hjk hjρ hN
        have hP : P j * (Real.exp B * f) ≤ Real.exp (-(k : ℝ)) := by
          have h := mul_le_mul_of_nonneg_right hpScale (show 0 ≤ Real.exp B * f by dsimp only [f]; positivity)
          exact h.trans (by dsimp only [B, f] at *; simpa only [mul_assoc, mul_left_comm, mul_comm] using hProduct)
        rw [hCV] at hband
        have hbase : 0 ≤ m * V := by dsimp only [m, V]; positivity
        have h := mul_le_mul_of_nonneg_left hP hbase
        have hbadd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₁ hbase) (Real.exp_nonneg (-(k : ℝ)))
        nlinarith only [hband, h, hbadd]
  have hSum : (∑ S ∈ F, ∑ T ∈ F, R S T) =
      ∑ j ∈ Finset.range (k + 1), ∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then R S T else 0 := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hSF
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    have hi : (S ∩ T).card ∈ Finset.range (k + 1) := by
      have h := (Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := T))).trans_eq (hS S hSF)
      exact Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single_of_mem _ hi (fun j _ hj ↦ ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
  have hMoment : (∑ S ∈ F, ∑ T ∈ F, R S T) ≤ K * (F.card : ℝ) ^ 2 := by
    rw [hSum]
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1), m * V * B₁ * W j := Finset.sum_le_sum hFull
      _ = m * V * B₁ * ∑ j ∈ Finset.range (k + 1), W j := by rw [Finset.mul_sum]
      _ ≤ m * V * B₁ * Q := mul_le_mul_of_nonneg_left hW (by dsimp only [m,V]; positivity)
      _ ≤ _ := by
        have hV : V ≤ 2 * m := by dsimp only [V, m]; linarith only [hHalf]
        have h := mul_le_mul_of_nonneg_right hV (show 0 ≤ m * B₁ * Q by positivity)
        dsimp only [K, m] at *
        nlinarith only [h]
  refine ⟨d, F, hEven, hd₀, hd₁, hd, hS, ?_⟩
  exact probability_event_union_ge_of_weighted_second_moment_bound ν F ⟨S₀, hS₀⟩ E
    (fun S _ ↦ measurableSet_inducedDegreeAtom S d) hPos hK hMoment

end BoundedEdgeRegularSubgraphs
