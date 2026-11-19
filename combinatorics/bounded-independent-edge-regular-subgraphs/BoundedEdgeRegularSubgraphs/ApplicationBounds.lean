module

public import BoundedEdgeRegularSubgraphs.BalancedBlockAmplification
public import BoundedEdgeRegularSubgraphs.LogarithmicAmplification
public import BoundedEdgeRegularSubgraphs.NoisyAndRandomEnvironment
public import BoundedEdgeRegularSubgraphs.DiagonalLargeCells
public import BoundedEdgeRegularSubgraphs.PowerOrderRates
import Mathlib.Tactic

/-!
# Structural rates and the independent-noise applications
-/

public section

open Filter MeasureTheory Set

namespace BoundedEdgeRegularSubgraphs

theorem eventually_power_order_failure {a c s : ℝ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    (Q : ∀ n : ℕ, (Edge (Fin n) → Icc (0 : ℝ) 1) → Prop)
    (h : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, (k : ℝ) ≤ a * (n : ℝ) ^ s →
      ∀ p : Edge (Fin n) → Icc (0 : ℝ) 1, Q n p → (graphLaw p).real (exactOrderEvent k)ᶜ ≤
        Real.exp (-c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ))) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Edge (Fin n) → Icc (0 : ℝ) 1, Q n p →
      (graphLaw p).real (exactOrderEvent ⌊a * (n : ℝ) ^ s⌋₊)ᶜ ≤
        Real.exp (-(c / a ^ (3 / 2 : ℝ)) * (n : ℝ) ^ (1 - s * (3 / 2))) := by
  let k (n : ℕ) := ⌊a * (n : ℝ) ^ s⌋₊
  have hk : Tendsto k atTop atTop := tendsto_floor_power_order ha hs
  filter_upwards [hk.eventually h, hk.eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (1 : ℕ)] with n hn hK hN
  intro p hp
  have hFloor : (k n : ℝ) ≤ a * (n : ℝ) ^ s := Nat.floor_le (by positivity)
  exact (hn n hFloor p hp).trans (exp_failure_le_of_power_order ha hc.le
    (Nat.cast_pos.mpr (zero_lt_one.trans_le hN)) (Nat.cast_pos.mpr (zero_lt_one.trans_le hK)) hFloor)

/-- Theorem 4.2 at the subcritical order given in the paper. -/
theorem eventually_subcritical_nearBalance {ξ M ε : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hM : 0 ≤ M) (hε : 0 < ε) (hε' : ε < 2 / 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let k := ⌊(n : ℝ) ^ (2 / 3 - ε)⌋₊
      ∀ q : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ q →
        (∃ p ∈ Icc ξ (1 - ξ), ∀ i, |degreeSum (fun e ↦ (q e : ℝ)) i / ((n : ℝ) - 1) - p| ≤
          Real.sqrt (M / k)) →
        (graphLaw q).real (exactOrderEvent k)ᶜ ≤ Real.exp (-c * (n : ℝ) ^ (3 * ε / 2)) := by
  obtain ⟨a, c, ha, hc, hMain⟩ := eventually_exactOrder_failure_le_of_nearBalance hξ hξ₁ hM
  let s := 2 / 3 - ε
  let K (n : ℕ) := ⌊(n : ℝ) ^ s⌋₊
  have hs : 0 < s := sub_pos.mpr hε'
  have hK : Tendsto K atTop atTop := by
    simpa only [K, one_mul] using tendsto_floor_power_order one_pos hs
  have hR := (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hK.eventually hMain, hK.eventually_ge_atTop (1 : ℕ),
    hR.eventually_ge_atTop (1 / a), eventually_ge_atTop (1 : ℕ)] with n hn hKn hRn hN
  intro k q hq hp
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (zero_lt_one.trans_le hN)
  have hk₀ : (0 : ℝ) < k := Nat.cast_pos.mpr (zero_lt_one.trans_le hKn)
  have hkP : (k : ℝ) ≤ (n : ℝ) ^ s := Nat.floor_le (by positivity)
  have hPow : (n : ℝ) ^ s ≤ a * (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [show (2 / 3 : ℝ) = s + ε by dsimp only [s]; ring, Real.rpow_add hn₀]
    have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).1 hRn) (Real.rpow_nonneg hn₀.le s)
    simpa only [Function.comp_apply, one_mul, mul_assoc, mul_left_comm, mul_comm] using h
  refine (hn n (hkP.trans hPow) q hq hp).trans ?_
  have h := exp_failure_le_of_power_order one_pos hc.le hn₀ hk₀ (by rw [one_mul]; exact hkP)
  rw [Real.one_rpow, div_one, show 1 - s * (3 / 2) = 3 * ε / 2 by dsimp only [s]; ring] at h
  exact h

/-- The independent-flip model inherits the uniform logarithmic result. -/
theorem eventually_logarithmic_noisyGraph {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ B : Edge (Fin n) → Bool,
      (graphLaw (noisyEdgeArray B hξ.le hξ₁.le)).real (atLeastOrderEvent ⌈c * Real.log n ^ 2⌉₊)ᶜ ≤
        (n : ℝ)⁻¹ := by
  obtain ⟨c, hc, h⟩ := eventually_logarithmic_regular_induced_subgraph hξ hξ₁
  exact ⟨c, hc, h.mono fun n hn B ↦ hn _ (noisyEdgeArray_floor B hξ.le hξ₁.le)⟩

/-- A regular deterministic base graph gives the exact-order bound in
Corollary 7.1 under the independent-flip law. -/
theorem eventually_exactOrder_noisyRegularGraph {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ k₀ n₀ : ℕ, 1 ≤ k₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k → (k : ℝ) ≤ a * (n : ℝ) ^ (2 / 3 : ℝ) →
      ∀ B : Edge (Fin n) → Bool,
        (∀ i j, degreeSum (fun e ↦ if B e then 1 else 0) i = degreeSum (fun e ↦ if B e then 1 else 0) j) →
        (graphLaw (noisyEdgeArray B hξ.le hξ₁.le)).real (exactOrderEvent k)ᶜ ≤
          Real.exp (-c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)) := by
  obtain ⟨a, c, ha, hc, k₀, n₀, hk₀, h⟩ := theorem1_1_equalDegrees ξ hξ hξ₁
  refine ⟨a, c, ha, hc, k₀, n₀, hk₀, fun n hn k hk hSize B hB ↦ ?_⟩
  exact h n hn k hk hSize _ (noisyEdgeArray_floor B hξ.le hξ₁.le)
    (noisyEdgeArray_equal_degree_means B hξ.le hξ₁.le hB)

/-- The failure rate at the chosen power-law order in Corollary 6.4. -/
theorem eventually_rank_power_order_failure {ξ : ℝ} {r : ℕ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hr : 0 < r) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ q : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ q → HasRankCompletion r q →
        (graphLaw q).real (exactOrderEvent ⌊a * (n : ℝ) ^ (4 / ((r : ℝ) + 7))⌋₊)ᶜ ≤
          Real.exp (-c * (n : ℝ) ^ (((r : ℝ) + 1) / ((r : ℝ) + 7))) := by
  obtain ⟨a, c, ha, hc, h⟩ := eventually_exactOrder_failure_le_of_largeBalancedCells hξ hξ₁
    (show 0 ≤ ((r : ℝ) + 1) / 2 by positivity)
    (show 0 < ((3 ^ r * (2 * (r : ℝ) ^ 2 + 1))⁻¹) by positivity)
    (show 0 ≤ 1 + (r : ℝ) ^ 2 by positivity)
  let s := 4 / ((r : ℝ) + 7)
  have he : 2 / (((r : ℝ) + 1) / 2 + 3) = s := by dsimp only [s]; field_simp <;> ring
  have hh := eventually_power_order_failure ha hc (show 0 < s by dsimp only [s]; positivity)
    (fun _ q ↦ HasFloor ξ q ∧ HasRankCompletion r q) (by
      filter_upwards [h] with k hk
      intro n hSize q hq
      apply hk n (by rwa [he]) q hq.1 (hasLargeBalancedCells_of_rank q hq.2))
  refine ⟨a, c / a ^ (3 / 2 : ℝ), ha, by positivity, ?_⟩
  filter_upwards [hh] with n hn
  intro q hq hRank
  have ht : 1 - s * (3 / 2) = ((r : ℝ) + 1) / ((r : ℝ) + 7) := by
    dsimp only [s]
    field_simp
    <;> ring
  simpa only [ht] using hn q ⟨hq, hRank⟩

/-- The failure rate at the chosen power-law order in Corollary 6.2. -/
theorem eventually_lipschitz_power_order_failure {ξ L : ℝ} {d : ℕ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hL : 0 ≤ L) (hd : 0 < d) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (x : Fin n → Fin d → Icc (0 : ℝ) 1)
        (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1),
        (∀ i j, W i j = W j i) → CubeLipschitz L W →
        (∀ i j, ξ ≤ (W i j : ℝ) ∧ (W i j : ℝ) ≤ 1 - ξ) →
        (graphLaw (fun e ↦ W (x e.val.1) (x e.val.2))).real
          (exactOrderEvent ⌊a * (n : ℝ) ^ (2 / ((d : ℝ) + 3))⌋₊)ᶜ ≤
          Real.exp (-c * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 3))) := by
  obtain ⟨a, c, ha, hc, h⟩ := eventually_exactOrder_failure_le_of_largeBalancedCells hξ hξ₁
    (Nat.cast_nonneg d) (show (0 : ℝ) < ((2 : ℝ) ^ d)⁻¹ by positivity) (show 0 ≤ 2 * L by positivity)
  let s := 2 / ((d : ℝ) + 3)
  have hh := eventually_power_order_failure ha hc (show 0 < s by dsimp only [s]; positivity)
    (fun _ q ↦ HasFloor ξ q ∧ HasLargeBalancedCells (d : ℝ) ((2 : ℝ) ^ d)⁻¹ (2 * L) q) (by
      filter_upwards [h] with k hk
      exact fun n hSize q hq ↦ hk n hSize q hq.1 hq.2)
  refine ⟨a, c / a ^ (3 / 2 : ℝ), ha, by positivity, ?_⟩
  filter_upwards [hh] with n hn
  intro x W hSymm hLip hFloor
  have ht : 1 - s * (3 / 2) = (d : ℝ) / ((d : ℝ) + 3) := by
    dsimp only [s]
    field_simp
    <;> ring
  simpa only [ht] using hn _ ⟨fun _ ↦ hFloor _ _, hasLargeBalancedCells_of_lipschitz x W hSymm hLip⟩

/-- The improved Lipschitz exponent under the hypothesis in Remark 6.5. -/
theorem eventually_quadratic_diagonal_order_failure {ξ L B : ℝ} {d : ℕ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      (k : ℝ) ≤ a * (n : ℝ) ^ (4 / ((d : ℝ) + 7)) →
      ∀ (x : Fin n → Fin d → Icc (0 : ℝ) 1)
        (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1),
        (∀ i j, W i j = W j i) → CubeLipschitz L W → CubeDiagonalQuadratic B W →
        (∀ i j, ξ ≤ (W i j : ℝ) ∧ (W i j : ℝ) ≤ 1 - ξ) →
        (graphLaw (fun e ↦ W (x e.val.1) (x e.val.2))).real (exactOrderEvent k)ᶜ ≤
          Real.exp (-c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)) := by
  obtain ⟨a, c, ha, hc, h⟩ := eventually_exactOrder_failure_le_of_largeBalancedCells hξ hξ₁
    (show 0 ≤ ((d : ℝ) + 1) / 2 by positivity)
    (show 0 < (((2 : ℝ) ^ d * (4 * L + 1))⁻¹) by positivity)
    (show 0 ≤ 1 + B by positivity)
  refine ⟨a, c, ha, hc, ?_⟩
  filter_upwards [h] with k hk
  intro n hSize x W hSymm hW hDiag hFloor
  have he : 2 / (((d : ℝ) + 1) / 2 + 3) = 4 / ((d : ℝ) + 7) := by
    field_simp
    <;> ring
  exact hk n (by rwa [he]) _ (fun e ↦ hFloor _ _)
    (hasLargeBalancedCells_of_diagonal_quadratic hL hB x W hSymm hW hDiag)

/-- The two uniform logarithmic failure bounds also hold after
averaging over a random environment, as in Corollary 7.3. -/
theorem eventually_logarithmic_random_environment {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ c c' : ℝ, 0 < c' ∧ c' ≤ c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ p : Θ → Edge (Fin n) → Icc (0 : ℝ) 1,
        AEMeasurable (fun t ↦ graphLaw (p t)) ν →
        (∀ᵐ t ∂ν, HasFloor ξ (p t)) →
        let μ := ν.bind (fun t ↦ graphLaw (p t))
        μ.real (atLeastOrderEvent ⌈c * Real.log n ^ 2⌉₊)ᶜ ≤ (n : ℝ)⁻¹ ∧
          μ.real (atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊)ᶜ ≤ Real.exp (-Real.sqrt n * Real.log n / 8) := by
  obtain ⟨c, c', hc', hc, n₀, _, h⟩ := theorem1_1_arbitrary ξ hξ hξ₁
  refine ⟨c, c', hc', hc, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro p hp hFloor
  exact ⟨probability_bind_graphLaw_le_of_ae ν p hp _ (measurableSet_atLeastOrderEvent _).compl
      (by positivity) (hFloor.mono fun t ht ↦ (h n hn (p t) ht).1),
    probability_bind_graphLaw_le_of_ae ν p hp _ (measurableSet_atLeastOrderEvent _).compl
      (Real.exp_nonneg _) (hFloor.mono fun t ht ↦ (h n hn (p t) ht).2)⟩

end BoundedEdgeRegularSubgraphs
