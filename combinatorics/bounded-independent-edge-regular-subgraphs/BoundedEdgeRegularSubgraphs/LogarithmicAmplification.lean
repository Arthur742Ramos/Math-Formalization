module

public import BoundedEdgeRegularSubgraphs.LogarithmicRegularity
public import BoundedEdgeRegularSubgraphs.ConsecutiveBlocks
public import BoundedEdgeRegularSubgraphs.AlmostSure
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Amplification of the logarithmic lower bound
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun m ↦ (eventually_ge_atTop (m ^ 2)).mono fun _ hn ↦ Nat.le_sqrt'.mpr hn

private theorem sqrt_half_le_nat_sqrt (n : ℕ) (hn : 4 ≤ n) :
    Real.sqrt n / 2 ≤ (n.sqrt : ℝ) := by
  have hnat := Nat.lt_succ_sqrt' n
  have hnat' : (n : ℝ) ≤ ((n.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast hnat.le
  have hS : Real.sqrt n ≤ (n.sqrt : ℝ) + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hnat'⟩
  have h₁ : 1 ≤ (n.sqrt : ℝ) := by exact_mod_cast Nat.le_sqrt'.2 (by omega : 1 ^ 2 ≤ n)
  linarith only [hS, h₁]

/-- The finite-probability conclusion of Corollary 7.2. The original
constant is any positive constant for which Theorem 5.3 holds. -/
theorem eventually_amplified_logarithmic_bound {ξ c c' : ℝ}
    (hc' : 0 < c') (hratio : c' < c / 4)
    (hSmall : ∀ᶠ m : ℕ in atTop, ∀ q : Edge (Fin m) → Icc (0 : ℝ) 1, HasFloor ξ q →
      (graphLaw q).real (atLeastOrderEvent ⌈c * Real.log m ^ 2⌉₊)ᶜ ≤ (m : ℝ)⁻¹) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ p →
      (graphLaw p).real (atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊)ᶜ ≤
        Real.exp (-Real.sqrt n * Real.log n / 8) := by
  classical
  let r := max (1 / 4 : ℝ) (Real.sqrt (c' / c))
  have hc : 0 < c := by linarith only [hc', hratio]
  have hr : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (le_max_left _ _)
  have hr₁ : r < 1 / 2 := by
    apply max_lt (by norm_num)
    have h : c' / c < (1 / 2 : ℝ) ^ 2 := by
      apply (div_lt_iff₀ hc).2
      linarith only [hratio]
    exact (Real.sqrt_lt' (by norm_num)).mpr h
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_nat_sqrt_atTop.eventually hSmall, eventually_ge_atTop (4 : ℕ),
    hlog.eventually_ge_atTop (Real.log 2 / (1 / 2 - r))] with n hLocal hn hL
  intro p hp
  let m := n.sqrt
  let b := n / m
  let S := consecutiveVertexBlock n m
  let L := Real.log n
  let t := ⌈c' * L ^ 2⌉₊
  let u := ⌈c * Real.log m ^ 2⌉₊
  have h₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hL₀ : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.sqrt_pos.mpr (by omega))
  have hmS : Real.sqrt n / 2 ≤ (m : ℝ) := sqrt_half_le_nat_sqrt n hn
  have hbm : (m : ℝ) ≤ b := by
    exact_mod_cast (Nat.le_div_iff_mul_le (Nat.sqrt_pos.mpr (by omega))).2 (Nat.sqrt_le n)
  have hlogm : r * L ≤ Real.log m := by
    have h := Real.log_le_log (by positivity : 0 < Real.sqrt n / 2) hmS
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt h₀.le] at h
    have hL' := (div_le_iff₀ (sub_pos.mpr hr₁)).1 hL
    linarith only [h, hL']
  have hLog₁ : L / 4 ≤ Real.log m := by
    have h := mul_le_mul_of_nonneg_right (le_max_left (1 / 4 : ℝ) (Real.sqrt (c'/c))) hL₀
    linarith only [h, hlogm]
  have htu : t ≤ u := by
    apply Nat.ceil_le_ceil
    have hroot : Real.sqrt (c' / c) * L ≤ Real.log m :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hL₀).trans hlogm
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (show 0 ≤ Real.sqrt (c' / c) * L by positivity) hroot 2) hc.le
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hh
    exact (by field_simp [hc.ne'] : c' * L ^ 2 = c * (c' / c * L ^ 2)).le.trans hh
  let E (i : Fin b) : Set (Edge ↥(S i) → ℝ) := (atLeastOrderEvent u)ᶜ
  have hE (i : Fin b) : (graphLaw (induce (S i) p)).real (E i) ≤ (m : ℝ)⁻¹ := by
    let f : Fin m ≃o ↥(S i) := (S i).orderIsoOfFin (card_consecutiveVertexBlock n m i)
    have h := hLocal (induce (S i) p ∘ edgeEquiv f) (fun e ↦ hp (inducedEdge _ (edgeEquiv f e)))
    rw [probability_atLeastOrder_failure_reindex] at h
    exact h
  have hSub : (atLeastOrderEvent t : Set (Edge (Fin n) → ℝ))ᶜ ⊆
      {w | ∀ i : Fin b, induce (S i) w ∈ E i} := by
    intro w hw i
    change induce (S i) w ∉ atLeastOrderEvent u
    intro hi
    exact hw (atLeastOrderEvent_mono htu (induce_preimage_atLeastOrder_subset (S i) u hi))
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  calc
    _ ≤ (graphLaw p).real {w | ∀ i : Fin b, induce (S i) w ∈ E i} := measureReal_mono hSub
    _ = ∏ i : Fin b, (graphLaw (induce (S i) p)).real (E i) :=
      probability_induced_disjoint_family p S (pairwise_disjoint_consecutiveVertexBlock n m)
        E (fun _ ↦ (measurableSet_atLeastOrderEvent u).compl)
    _ ≤ ∏ _i : Fin b, (m : ℝ)⁻¹ := Finset.prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) (fun i _ ↦ hE i)
    _ = Real.exp (-(b : ℝ) * Real.log m) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_log hm, ← Real.exp_neg, ← Real.exp_nat_mul]
      rw [Real.exp_log hm]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul (hmS.trans hbm) hLog₁ (by positivity : 0 ≤ L / 4)
        (show 0 ≤ (b : ℝ) by positivity)
      nlinarith only [h]

/-- The almost-sure conclusion in Corollary 7.2 for any coupling
with the specified marginal laws. -/
theorem ae_eventually_logarithmic_regular_induced_subgraph
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ξ c c' : ℝ} (hc' : 0 < c') (hratio : c' < c / 4)
    (hSmall : ∀ᶠ m : ℕ in atTop, ∀ q : Edge (Fin m) → Icc (0 : ℝ) 1, HasFloor ξ q →
      (graphLaw q).real (atLeastOrderEvent ⌈c * Real.log m ^ 2⌉₊)ᶜ ≤ (m : ℝ)⁻¹)
    (p : (n : ℕ) → Edge (Fin n) → Icc (0 : ℝ) 1) (hp : ∀ n, HasFloor ξ (p n))
    (X : (n : ℕ) → Ω → (Edge (Fin n) → ℝ))
    (hX : ∀ n, MeasurePreserving (X n) μ (graphLaw (p n))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, X n ω ∈ atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊ := by
  obtain ⟨n₀, h⟩ := eventually_atTop.mp (eventually_amplified_logarithmic_bound hc' hratio hSmall)
  let E (n : ℕ) : Set (Edge (Fin n) → ℝ) := atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊
  let A (n : ℕ) := (X n) ⁻¹' (E n)
  have hFail (n : ℕ) (hn : n₀ ≤ n) : μ.real (A n)ᶜ ≤ Real.exp (-Real.sqrt n * Real.log n / 8) := by
    have hmap := (hX n).measure_preimage
      (measurableSet_atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊).compl.nullMeasurableSet
    change μ (A n)ᶜ = graphLaw (p n) (E n)ᶜ at hmap
    rw [measureReal_def, hmap, ← measureReal_def]
    exact h n hn (p n) (hp n)
  exact ae_eventually_success_of_amplified_failure μ A n₀ hFail

/-- The two uniform bounds in Theorem 1.1(1). -/
theorem theorem1_1_arbitrary : Theorem1_1_arbitrary := by
  intro ξ hξ hξ₁
  obtain ⟨c, hc, hBasic⟩ := eventually_logarithmic_regular_induced_subgraph hξ hξ₁
  let c' := c / 8
  have hc' : 0 < c' := by dsimp only [c']; positivity
  have hAmp := eventually_amplified_logarithmic_bound hc' (by dsimp only [c']; linarith) hBasic
  have hBoth := hBasic.and (hAmp.and (eventually_ge_atTop (1 : ℕ)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hBoth
  refine ⟨c, c', hc', by dsimp only [c']; linarith, n₀, (hn₀ n₀ le_rfl).2.2, ?_⟩
  intro n hn p hp
  exact ⟨(hn₀ n hn).1 p hp, (hn₀ n hn).2.1 p hp⟩

end BoundedEdgeRegularSubgraphs
