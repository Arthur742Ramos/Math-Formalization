module

public import BoundedEdgeRegularSubgraphs.NearBalanceTransfer
public import BoundedEdgeRegularSubgraphs.LinearProductStructure
public import BoundedEdgeRegularSubgraphs.PowerOrderRates
import Mathlib.Tactic

/-!
# The matching square-root lower bound for the linear product array
-/

public section

open Filter MeasureTheory Set Function
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

theorem probability_linear_product_lower_tendsto_zero (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (htop : a + b < 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ p : (n : ℕ) → Edge (Fin n) → Icc (0 : ℝ) 1,
      (∀ n e, (p n e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) →
      Tendsto (fun n ↦ (graphLaw (p n)).real (atLeastOrderEvent ⌈A * Real.sqrt n⌉₊)ᶜ) atTop (𝓝 0) := by
  let ξ := min (a ^ 2 / 2) ((1 - (a + b) ^ 2) / 2)
  have ha' : a < 1 := by linarith only [htop, hb]
  have hab₀ : 0 < a + b := by positivity
  have htop' : (a + b) ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ htop hab₀.le (show (2 : ℕ) ≠ 0 by norm_num)
    simpa only [one_pow] using h
  have hξ : 0 < ξ := lt_min (by positivity) (by linarith only [htop'])
  have hξ₁ : ξ < 1 / 2 := (min_le_left _ _).trans_lt (by
    have h : a ^ 2 < 1 := by
      simpa only [one_pow] using pow_lt_pow_left₀ ha' ha.le (show (2 : ℕ) ≠ 0 by norm_num)
    linarith only [h])
  obtain ⟨L, c, hL, hc, k₀, n₀, hk₀, hGraph⟩ := theorem1_1_lipschitz ξ b 1 hξ hξ₁ hb.le (by omega)
  let k (n : ℕ) := ⌊L * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊
  let W := linearProductKernel a b ha.le hb.le htop.le
  have hSymm (x y : UnitCubeLine) : W x y = W y x := Subtype.ext (mul_comm _ _)
  have hLip := linearProductKernel_lipschitz a b ha.le hb.le htop.le
  have hBound (x y : UnitCubeLine) : ξ ≤ (W x y : ℝ) ∧ (W x y : ℝ) ≤ 1 - ξ := by
    obtain ⟨hx₁, hx₂⟩ := linearWeight_mem (a := a) hb.le x
    obtain ⟨hy₁, hy₂⟩ := linearWeight_mem (a := a) hb.le y
    change ξ ≤ (a + b * (x 0 : ℝ)) * (a + b * (y 0 : ℝ)) ∧
      (a + b * (x 0 : ℝ)) * (a + b * (y 0 : ℝ)) ≤ 1 - ξ
    have hl := mul_le_mul hx₁ hy₁ ha.le (ha.le.trans hx₁)
    have hu := mul_le_mul hx₂ hy₂ (ha.le.trans hy₁) hab₀.le
    have hl' : ξ ≤ a * a := (min_le_left _ _).trans (by nlinarith only [sq_nonneg a])
    have hu' : (a + b) * (a + b) ≤ 1 - ξ := by
      have h := min_le_right (a ^ 2 / 2) ((1 - (a + b) ^ 2) / 2)
      nlinarith only [h, htop']
    exact ⟨hl'.trans hl, hu.trans hu'⟩
  refine ⟨L / 2, by positivity, ?_⟩
  intro p hp
  have hK : Tendsto k atTop atTop := tendsto_floor_power_order hL (by norm_num)
  have hRate : ∀ᶠ n : ℕ in atTop, (graphLaw (p n)).real (atLeastOrderEvent ⌈L / 2 * Real.sqrt n⌉₊)ᶜ ≤
      Real.exp (-(c / L ^ (3 / 2 : ℝ)) * (n : ℝ) ^ (1 / 4 : ℝ)) := by
    filter_upwards [eventually_floor_power_order_bounds hL (show (0 : ℝ) < 1 / 2 by norm_num),
      hK.eventually_ge_atTop k₀, eventually_ge_atTop (max n₀ 1)] with n hn hk hN
    have hn₀ : 0 < n := by omega
    let x (i : Fin n) (_ : Fin 1) : Icc (0 : ℝ) 1 :=
      ⟨((i.val : ℝ) + 1) / n, ⟨by positivity, (div_le_one (Nat.cast_pos.mpr hn₀)).2 (by
        exact_mod_cast Nat.succ_le_of_lt i.isLt)⟩⟩
    have hEq : (fun e : Edge (Fin n) ↦ W (x e.val.1) (x e.val.2)) = p n := by
      funext e
      apply Subtype.ext
      rw [hp n e]
      dsimp only [W, linearProductKernel, x, linearVertexWeight]
      simp only [mul_div_assoc]
    have hs : (k n : ℝ) ≤ L * (n : ℝ) ^ (2 / ((1 : ℕ) + 3) : ℝ) := by norm_num; exact hn.2
    have h₁ := hGraph n ((le_max_left _ _).trans hN) (k n) hk hs W hSymm hLip hBound x
    rw [hEq] at h₁
    have hThreshold : ⌈L / 2 * Real.sqrt n⌉₊ ≤ k n := by
      apply Nat.ceil_le.mpr
      rw [Real.sqrt_eq_rpow]
      convert hn.1 using 1 <;> ring
    have : IsProbabilityMeasure (graphLaw (p n)) := by unfold graphLaw; infer_instance
    refine (measureReal_mono (compl_subset_compl.mpr (exactOrderEvent_subset_atLeastOrderEvent hThreshold))).trans
      (h₁.trans ?_)
    have h := exp_failure_le_of_power_order hL hc.le (Nat.cast_pos.mpr hn₀)
      (Nat.cast_pos.mpr (zero_lt_one.trans_le (hk₀.trans hk))) hn.2
    rw [show 1 - (1 / 2 : ℝ) * (3 / 2) = 1 / 4 by norm_num] at h
    exact h
  have hf : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun n : ℕ ↦ (c / L ^ (3 / 2 : ℝ)) * (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    hf.const_mul_atTop (by positivity)
  have hlim : Tendsto (fun n : ℕ ↦ Real.exp (-(c / L ^ (3 / 2 : ℝ)) * (n : ℝ) ^ (1 / 4 : ℝ)))
      atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hg)
    change Tendsto (fun n : ℕ ↦ Real.exp (-(c / L ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ))))
      atTop (𝓝 0) at hh
    simpa only [neg_mul] using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hRate

/-- The two-sided square-root conclusion of Theorem 8.2. -/
theorem probability_linear_product_square_root_window (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (htop : a + b < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ p : (n : ℕ) → Edge (Fin n) → Icc (0 : ℝ) 1,
      (∀ n e, (p n e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) →
      Tendsto (fun n ↦ (graphLaw (p n)).real
        (atLeastOrderEvent ⌈A * Real.sqrt n⌉₊ ∩ (atLeastOrderEvent ⌈B * Real.sqrt n⌉₊)ᶜ))
        atTop (𝓝 1) := by
  obtain ⟨A, hA, hLower⟩ := probability_linear_product_lower_tendsto_zero a b ha hb htop
  obtain ⟨B, hB, hUpper⟩ := probability_linear_product_upper_tendsto_zero a b ha hb htop
  refine ⟨A, B, hA, hB, ?_⟩
  intro p hp
  let E (n : ℕ) : Set (Edge (Fin n) → ℝ) := atLeastOrderEvent ⌈A * Real.sqrt n⌉₊
  let F (n : ℕ) : Set (Edge (Fin n) → ℝ) := atLeastOrderEvent ⌈B * Real.sqrt n⌉₊
  have hLim : Tendsto (fun n ↦ (graphLaw (p n)).real (E n)ᶜ + (graphLaw (p n)).real (F n)) atTop (𝓝 0) := by
    simpa only [add_zero] using (hLower p hp).add (hUpper p hp)
  have hZero : Tendsto (fun n ↦ (graphLaw (p n)).real (E n ∩ (F n)ᶜ)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim
      (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    apply Eventually.of_forall
    intro n
    simpa only [compl_inter, compl_compl] using measureReal_union_le (μ := graphLaw (p n)) (E n)ᶜ (F n)
  have hAbs (n : ℕ) : (graphLaw (p n)).real (E n ∩ (F n)ᶜ) =
      1 - (graphLaw (p n)).real (E n ∩ (F n)ᶜ)ᶜ := by
    have : IsProbabilityMeasure (graphLaw (p n)) := by unfold graphLaw; infer_instance
    rw [probReal_compl_eq_one_sub ((measurableSet_atLeastOrderEvent _).inter (measurableSet_atLeastOrderEvent _).compl)]
    ring
  change Tendsto (fun n ↦ (graphLaw (p n)).real (E n ∩ (F n)ᶜ)) atTop (𝓝 1)
  simp_rw [hAbs]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hZero

end BoundedEdgeRegularSubgraphs
