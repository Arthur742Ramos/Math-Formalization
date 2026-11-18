module

public import BoundedEdgeRegularSubgraphs.ProductVariation
public import BoundedEdgeRegularSubgraphs.WeightedSubsets
import BoundedEdgeRegularSubgraphs.GaussianSum
import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic

/-!
# The upper bound for the linear product array
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The vertex weight in the rank-one example of Theorem 8.2. -/
@[expose] noncomputable def linearVertexWeight (a b : ℝ) {n : ℕ} (i : Fin n) : ℝ :=
  a + b * ((i.val : ℝ) + 1) / n

private theorem linearVertexWeight_bounds {a b : ℝ} (hb : 0 < b) {n : ℕ} (i : Fin n) :
    linearVertexWeight a b i ∈ Set.Icc a (a + b) := by
  unfold linearVertexWeight
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (i.isLt.pos)
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hi₀ : 0 ≤ (i.val : ℝ) + 1 := by positivity
  constructor
  · linarith [div_nonneg (mul_nonneg hb.le hi₀) hn.le]
  · have h : b * ((i.val : ℝ) + 1) / n ≤ b :=
      (div_le_iff₀ hn).mpr (mul_le_mul_of_nonneg_left hi hb.le)
    linarith

private theorem linearVertexWeight_diff {a b : ℝ} (hb : 0 < b) {n : ℕ} (i j : Fin n) :
    |linearVertexWeight a b i - linearVertexWeight a b j| =
      (b / (n : ℝ)) * |(i.val : ℝ) - j.val| := by
  unfold linearVertexWeight
  rw [show a + b * ((i.val : ℝ) + 1) / n - (a + b * ((j.val : ℝ) + 1) / n) =
    (b / n) * ((i.val : ℝ) - j.val) by ring, abs_mul, abs_of_nonneg (by positivity)]

private theorem gaussian_union_product_factorial {n k : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    {C K : ℝ} (hC : 0 < C) (hK : 1 ≤ K) :
    (n : ℝ) * (C / Real.sqrt k) ^ k *
      ((K * n / Real.sqrt k) ^ (k - 1) / ((k - 1).factorial : ℝ)) ≤
        ((k : ℝ) * Real.sqrt k) * (C * K * Real.exp 1 * n / (k : ℝ) ^ 2) ^ k := by
  have hk₀ : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk₀
  have hsk2 := Real.sq_sqrt hk₀.le
  have hK₀ : 0 < K := by linarith
  have hfac : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
    nth_rw 1 [show k = (k - 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 1
    exact_mod_cast (show k - 1 + 1 = k by omega)
  let t : ℝ := K * n / Real.sqrt k
  have ht : 0 < t := by dsimp [t]; positivity
  have hp : t ^ k = t ^ (k - 1) * t := by
    nth_rw 1 [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  calc
    _ = (((k : ℝ) * Real.sqrt k) / K) *
        ((C * K * n / k) ^ k / k.factorial) := by
      have heq : (C * K * n / k) = (C / Real.sqrt k) * t := by
        dsimp [t]
        field_simp
        exact hsk2
      rw [heq, mul_pow, hp, hfac]
      dsimp [t]
      field_simp
    _ ≤ ((k : ℝ) * Real.sqrt k) *
        ((C * K * n / k) ^ k / k.factorial) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_self (by positivity) hK
    _ ≤ ((k : ℝ) * Real.sqrt k) *
        ((C * K * n / k) ^ k / ((k : ℝ) / Real.exp 1) ^ k) := by
      gcongr
      exact exp_pow_le_factorial k (by omega)
    _ = _ := by
      rw [← div_pow]
      congr 2
      field_simp

/-- The finite weighted first-moment estimate in the proof of Theorem 8.2. -/
theorem probability_linear_product_exact_order_le (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (htop : a + b < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ n k : ℕ, 3 ≤ k → k ≤ n →
      ∀ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1,
      (∀ e, (p e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) →
      (graphLaw p).real (exactOrderEvent k) ≤
        ((k : ℝ) * Real.sqrt k) * (D * n / (k : ℝ) ^ 2) ^ k := by
  let ξ := min (a ^ 2) (min (1 - (a + b) ^ 2) (1 / 4 : ℝ))
  have htop' : (a + b) ^ 2 < 1 := by nlinarith only [mul_pos (show 0 < 1 - (a + b) by linarith) (show 0 < 1 + (a + b) by linarith)]
  have hξ : 0 < ξ := lt_min (sq_pos_of_pos ha)
    (lt_min (sub_pos.mpr htop') (by norm_num))
  have hξ' : ξ < 1 / 2 :=
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨C, hC, hbound⟩ := probability_regular_le_variation_gaussian_finite ξ hξ hξ'
  let θ := (a * b) ^ 2 / 3
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let K := 2 + Real.sqrt (Real.pi / θ)
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.sqrt_nonneg (Real.pi / θ)]
  refine ⟨C * K * Real.exp 1, by positivity, ?_⟩
  intro n k hk hkn p hp
  classical
  have hk₀ : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk₃ : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnₖ : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h2 : 0 < (k : ℝ) - 2 := by linarith
  let r := θ * k / ((n : ℝ) ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  let w (v i : Fin n) := Real.exp (-r * ((i.val : ℝ) - v.val) ^ 2)
  let B := (C / Real.sqrt k) ^ k
  have hB : 0 < B := by dsimp [B]; positivity
  let f (S : Finset (Fin n)) := (graphLaw p).real (inducedRegularEvent S) / B
  have hfloor (e : Edge (Fin n)) : ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ := by
    obtain ⟨h₁, h₂⟩ := linearVertexWeight_bounds (a := a) hb e.val.1
    obtain ⟨h₃, h₄⟩ := linearVertexWeight_bounds (a := a) hb e.val.2
    rw [hp]
    constructor
    · exact (min_le_left _ _).trans (by
        rw [sq]
        exact mul_le_mul h₁ h₃ ha.le (ha.le.trans h₁))
    · have ht : ξ ≤ 1 - (a + b) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
      have h := mul_le_mul h₂ h₄ (ha.le.trans h₃) (by linarith : 0 ≤ a + b)
      nlinarith only [h, ht]
  have hpoint (S : Finset (Fin n)) (hS : S.card = k) : ∃ v ∈ S, f S ≤ ∏ i ∈ S, w v i := by
    have hS' : Fintype.card ↥S = k := (Fintype.card_coe S).trans hS
    let z (i : ↥S) := linearVertexWeight a b i.val
    let x (i : ↥S) : ℝ := i.val.val
    obtain ⟨v, hv⟩ := degreeVariation_product_anchor (by rwa [hS']) (induce S p) z x
      ha.le (div_nonneg hb.le hn₀.le) (fun i ↦ (linearVertexWeight_bounds hb i.val).1)
      (fun e ↦ hp (inducedEdge S e)) (fun i j ↦ (linearVertexWeight_diff hb i.val j.val).ge)
    rw [hS'] at hv
    let L := ∑ i : ↥S, (x i - x v) ^ 2
    have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have hvar : r * L ≤ 2 * degreeVariation (induce S p) / ((k : ℝ) - 2) := by
      apply (le_div_iff₀ h2).mpr
      have hc : r * ((k : ℝ) - 2) ≤ (a * (b / n)) ^ 2 * ((k : ℝ) - 2) ^ 2 := by

        dsimp only [r, θ]
        apply (le_of_mul_le_mul_right (a := (n : ℝ) ^ 2)) _ (sq_pos_of_pos hn₀)
        field_simp
        linarith only [hk₃]
      rw [mul_right_comm]
      exact (mul_le_mul_of_nonneg_right hc hL).trans hv
    refine ⟨v.val, v.property, ?_⟩
    have h := hbound (by rwa [hS']) (induce S p) (fun e ↦ hfloor (inducedEdge S e))
    rw [hS', ← probability_induced_regular_eq] at h
    have heq : (∏ i ∈ S, w v.val i) = Real.exp (-(r * L)) := by
      dsimp only [w, L]
      rw [← Real.exp_sum, ← Finset.mul_sum, neg_mul]
      have hs := Finset.sum_coe_sort S (fun i : Fin n ↦ ((i.val : ℝ) - v.val.val) ^ 2)
      rw [← hs]
    rw [heq]
    change (graphLaw p).real (inducedRegularEvent S) / B ≤ _
    apply (div_le_iff₀ hB).mpr
    rw [mul_comm _ B]
    have he : -2 * degreeVariation (induce S p) / ((k : ℝ) - 2) ≤ -(r * L) := by
      simpa only [neg_mul, neg_div] using neg_le_neg hvar
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB.le)
  have hgauss (v : Fin n) : (∑ i : Fin n, w v i) ≤ K * n / Real.sqrt k := by
    have hs := gaussian_sum_fin_le n v hr
    have hroot : Real.sqrt (Real.pi / r) = Real.sqrt (Real.pi / θ) * (n / Real.sqrt k) := by
      have hid : Real.pi / r = (Real.pi / θ) * (((n : ℝ) ^ 2) / k) := by
        dsimp only [r]
        field_simp
      rw [hid, Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg (n : ℝ)),
        Real.sqrt_sq hn₀.le]
    have hnk : Real.sqrt k ≤ (n : ℝ) := by
      have hk₁ : (1 : ℝ) ≤ k := by linarith
      have hn₁ : 1 ≤ (n : ℝ) := hk₁.trans hnₖ
      apply (Real.sqrt_le_left (Nat.cast_nonneg n)).mpr
      exact hnₖ.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hn₁) hn₀.le])
    have hratio : (1 : ℝ) ≤ n / Real.sqrt k :=
      (le_div_iff₀ (Real.sqrt_pos.2 hk₀)).mpr (by simpa only [one_mul] using hnk)
    rw [hroot] at hs
    dsimp only [K]
    calc
      _ ≤ _ := hs
      _ ≤ _ := by rw [mul_div_assoc]; linarith only [hratio]
  have hs := sum_le_anchored_subsets k f w (fun _ _ ↦ Real.exp_nonneg _)
    (fun _ ↦ by simp [w]) hpoint
  have hsum : (∑ S : {S : Finset (Fin n) // S.card = k}, f S.val) ≤
      (n : ℝ) * ((K * n / Real.sqrt k) ^ (k - 1) / ((k - 1).factorial : ℝ)) := by
    refine hs.trans ?_
    have hpt (v : Fin n) : (∑ i, w v i) ^ (k - 1) / ((k - 1).factorial : ℝ) ≤
        (K * n / Real.sqrt k) ^ (k - 1) / ((k - 1).factorial : ℝ) := by
      gcongr
      exact hgauss v
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) ↦ hpt v)
  calc
    _ ≤ ∑ S : {S : Finset (Fin n) // S.card = k},
        (graphLaw p).real (inducedRegularEvent S.val) := measureReal_iUnion_fintype_le _
    _ = B * ∑ S : {S : Finset (Fin n) // S.card = k}, f S.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [f]
      field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum hB.le).trans (by
      rw [← mul_assoc, mul_comm B]
      exact gaussian_union_product_factorial hk hkn hC hK)

private theorem square_le_two_pow_succ (l : ℕ) (hl : 3 ≤ l) :
    (l : ℝ) ^ 2 ≤ (2 : ℝ) ^ (l + 1) := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases h : 3 ≤ l
    · have h' : (3 : ℝ) ≤ l := by exact_mod_cast h
      have hs : ((l : ℝ) + 1) ^ 2 ≤ 2 * (l : ℝ) ^ 2 := by
        nlinarith only [h', sq_nonneg ((l : ℝ) - 3)]
      rw [Nat.cast_succ, pow_succ' (2 : ℝ) (l + 1)]
      exact hs.trans (mul_le_mul_of_nonneg_left (ih h) (by norm_num))
    · have hl' : l = 2 := by omega
      subst l
      norm_num

/-- Above a constant times the square root of the ambient order, the upper
tail in Theorem 8.2 decays at least geometrically. -/
theorem probability_linear_product_at_least_order_le (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (htop : a + b < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ n k : ℕ, 3 ≤ k → 4 * D * n ≤ (k : ℝ) ^ 2 →
      ∀ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1,
      (∀ e, (p e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) →
      (graphLaw p).real (atLeastOrderEvent k) ≤ 4 * (1 / 2 : ℝ) ^ k := by
  obtain ⟨D, hD, h⟩ := probability_linear_product_exact_order_le a b ha hb htop
  refine ⟨D, hD, ?_⟩
  intro n k hk hcut p hp
  have hpt (l : ℕ) (hl : l ∈ Finset.Icc k n) :
      (graphLaw p).real (exactOrderEvent l) ≤ 2 * (1 / 2 : ℝ) ^ l := by
    have ⟨hkl, hln⟩ := Finset.mem_Icc.mp hl
    have hl₃ := hk.trans hkl
    have hl₁ : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
    have hl₀ : (0 : ℝ) < l := by linarith
    have hrate : D * n / (l : ℝ) ^ 2 ≤ 1 / 4 := by
      have hc : (k : ℝ) ≤ l := by exact_mod_cast hkl
      have hs := (sq_le_sq₀ (Nat.cast_nonneg k) hl₀.le).mpr hc
      apply (div_le_iff₀ (sq_pos_of_pos hl₀)).mpr
      linarith only [hcut.trans hs]
    have hsize : (l : ℝ) * Real.sqrt l ≤ (2 : ℝ) ^ (l + 1) := by
      have hsq : (l : ℝ) ≤ (l : ℝ) ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hl₁) hl₀.le]
      have hs : Real.sqrt (l : ℝ) ≤ l := (Real.sqrt_le_left hl₀.le).mpr hsq
      refine (mul_le_mul_of_nonneg_left hs hl₀.le).trans ?_
      rw [← pow_two]
      exact square_le_two_pow_succ l hl₃
    calc
      _ ≤ ((l : ℝ) * Real.sqrt l) * (D * n / (l : ℝ) ^ 2) ^ l := h n l hl₃ hln p hp
      _ ≤ (2 : ℝ) ^ (l + 1) * (1 / 4 : ℝ) ^ l := by
        apply mul_le_mul hsize (pow_le_pow_left₀ (by positivity) hrate l) (by positivity) (by positivity)
      _ = _ := by rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
  rw [atLeastOrderEvent_eq_iUnion_exactOrderEvent, Fintype.card_fin]
  refine (measureReal_biUnion_finset_le _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  rw [← Finset.mul_sum, ← Finset.Ico_succ_right_eq_Icc]
  calc
    _ ≤ (2 : ℝ) * ((1 / 2 : ℝ) ^ k / (1 - 1 / 2)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)) (by norm_num)
    _ = _ := by ring


/-- The square-root upper conclusion of Theorem 8.2. -/
theorem probability_linear_product_upper_tendsto_zero (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (htop : a + b < 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ p : (n : ℕ) → Edge (Fin n) → Set.Icc (0 : ℝ) 1,
      (∀ n e, (p n e : ℝ) = linearVertexWeight a b e.val.1 * linearVertexWeight a b e.val.2) →
      Filter.Tendsto (fun n ↦ (graphLaw (p n)).real (atLeastOrderEvent ⌈A * Real.sqrt n⌉₊))
        Filter.atTop (nhds 0) := by
  obtain ⟨D, hD, h⟩ := probability_linear_product_at_least_order_le a b ha hb htop
  let A := max 3 (Real.sqrt (4 * D))
  have hA : 3 ≤ A := le_max_left _ _
  refine ⟨A, by linarith, ?_⟩
  intro p hp
  let k (n : ℕ) := ⌈A * Real.sqrt n⌉₊
  have hA₀ : 0 ≤ A := by linarith
  have hceil (n : ℕ) : A * Real.sqrt n ≤ k n := Nat.le_ceil _
  have hlim : Filter.Tendsto k Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro m
    filter_upwards [Filter.eventually_ge_atTop (m ^ 2)] with n hn
    have hs : (m : ℝ) ≤ Real.sqrt n := by
      apply (Real.le_sqrt (Nat.cast_nonneg m) (Nat.cast_nonneg n)).2
      exact_mod_cast hn
    have ht : Real.sqrt n ≤ A * Real.sqrt n := by
      exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (by linarith)
    exact_mod_cast hs.trans (ht.trans (hceil n))
  have hupper : ∀ᶠ n in Filter.atTop, (graphLaw (p n)).real (atLeastOrderEvent (k n)) ≤
      4 * (1 / 2 : ℝ) ^ k n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 1 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using hn')
    have hk₃ : 3 ≤ k n := by
      have hx : (3 : ℝ) ≤ (k n : ℝ) :=
        hA.trans ((le_mul_of_one_le_right hA₀ hs).trans (hceil n))
      exact_mod_cast hx
    have hbase : Real.sqrt (4 * D) * Real.sqrt n ≤ (k n : ℝ) :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)).trans (hceil n)
    have hsq := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg (k n))).mpr hbase
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * D), Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))] at hsq
    exact h n (k n) hk₃ hsq (p n) (hp n)
  have hzero : Filter.Tendsto (fun n ↦ 4 * (1 / 2 : ℝ) ^ k n) Filter.atTop (nhds 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp hlim
    simpa only [mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := (4 : ℝ))).mul hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hupper


end BoundedEdgeRegularSubgraphs
