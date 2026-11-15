/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.CellBounds
public import ErdosOverlap.Numerics.ConjugateError
public import ErdosOverlap.Numerics.PolynomialIntegration

/-!
# Continuous integral semantics of finite polynomial leaves

The pointwise bounds are required only in the open interior of each leaf.
This permits arbitrary endpoint conventions for the piecewise linear dual
derivative. Exact rational polynomial integration and finite adjacency then
give a bound for the genuine integral over the entire covered interval.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory Set

public section

@[expose] noncomputable def expandedMinorant
    (A B L K V lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ : ℝ) : ℝ :=
  sA * (alpha₁ * K + alpha₂ * V) * A +
    (rho * L - sigma * alpha₁ * K + sB * alpha₂ * V) * B -
    |lam| * (alpha₁ * K + alpha₂ * V) - beta₁ * K - beta₂ * V

theorem conjugate_expanded_minorant
    {A B L U K V lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hK : K = min U L) (hV : V = U - K)
    (hsA : -1 ≤ sA ∧ sA ≤ 1) (hsB : -1 ≤ sB ∧ sB ≤ 1)
    (hrho : 0 ≤ rho ∧ rho ≤ 1) (hsigma : 0 ≤ sigma ∧ sigma ≤ 1)
    (h₁ : max (|lam| - sA * A + sigma * B) 0 ≤
      alpha₁ * (|lam| - sA * A + sigma * B) + beta₁)
    (h₂ : max (|lam| - sA * A - sB * B) 0 ≤
      alpha₂ * (|lam| - sA * A - sB * B) + beta₂) :
    expandedMinorant A B L K V lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ ≤
      profileConjugate (max B 0) (|A| + |B|) L U lam := by
  have h := conjugate_affine_minorant hL hU hsA hsB hrho hsigma h₁ h₂
  rw [hV, hK]
  convert h using 1
  unfold expandedMinorant
  ring

/-- No sign agreement between the true and approximating kernel is assumed.
The uniform error cost is at most `2*delta` when both capacities lie in `[0,1]`. -/
theorem actual_conjugate_expanded_minorant
    {A B PA PB L U K V lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ delta : ℝ}
    (hL : 0 ≤ L ∧ L ≤ 1) (hU : 0 ≤ U ∧ U ≤ 1)
    (hK : K = min U L) (hV : V = U - K)
    (hsA : -1 ≤ sA ∧ sA ≤ 1) (hsB : -1 ≤ sB ∧ sB ≤ 1)
    (hrho : 0 ≤ rho ∧ rho ≤ 1) (hsigma : 0 ≤ sigma ∧ sigma ≤ 1)
    (h₁ : max (|lam| - sA * PA + sigma * PB) 0 ≤
      alpha₁ * (|lam| - sA * PA + sigma * PB) + beta₁)
    (h₂ : max (|lam| - sA * PA - sB * PB) 0 ≤
      alpha₂ * (|lam| - sA * PA - sB * PB) + beta₂)
    (hdelta : 0 ≤ delta) (hA : |A - PA| ≤ delta) (hB : |B - PB| ≤ delta) :
    expandedMinorant PA PB L K V lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ -
      2 * delta ≤ profileConjugate (max B 0) (|A| + |B|) L U lam := by
  have hm := conjugate_expanded_minorant hL.1 hU.1 hK hV hsA hsB hrho hsigma h₁ h₂
  have he := physical_profileConjugate_error_le (lam := lam) hL.1 hU.1 hA hB
  have hmax : max L U ≤ 1 := max_le hL.2 hU.2
  have hcost : U * delta + max L U * delta ≤ 2 * delta := by
    have hleft := mul_le_mul_of_nonneg_right hU.2 hdelta
    have hright := mul_le_mul_of_nonneg_right hmax hdelta
    nlinarith
  have hlower := (abs_le.mp (he.trans hcost)).1
  linarith

theorem positivePart_le_affine_of_approx {A PA alpha beta delta : ℝ}
    (hA : |A - PA| ≤ delta) (hP : max PA 0 ≤ alpha * PA + beta) :
    max A 0 ≤ alpha * PA + beta + delta := by
  have h := (le_abs_self (max A 0 - max PA 0)).trans
    ((abs_max_sub_max_le_abs A PA 0).trans hA)
  linarith

/-- A compatible pointwise majorant for the denominator integrand. Its
two positive parts and outer factor two give the explicit `4*delta` margin. -/
theorem denominator_upper_of_approx {A B PA PB alphaA betaA alphaB betaB delta : ℝ}
    (hA : |A - PA| ≤ delta) (hB : |B - PB| ≤ delta)
    (hPA : max PA 0 ≤ alphaA * PA + betaA)
    (hPB : max PB 0 ≤ alphaB * PB + betaB) :
    2 * (max A 0 + max B 0) ≤
      2 * alphaA * PA + 2 * alphaB * PB + 2 * (betaA + betaB) + 4 * delta := by
  have ha := positivePart_le_affine_of_approx hA hPA
  have hb := positivePart_le_affine_of_approx hB hPB
  linarith

theorem integral_lower_of_pointwise_margin {f g : ℝ → ℝ} {l r margin : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hpoint : ∀ t ∈ Ioo l r, g t - margin ≤ f t) :
    (∫ t in l..r, g t) - margin * (r - l) ≤ ∫ t in l..r, f t := by
  have hc : IntervalIntegrable (fun _ : ℝ => margin) volume l r := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hlr (hg.sub hc) hf hpoint
  rw [intervalIntegral.integral_sub hg hc, intervalIntegral.integral_const] at hm
  convert hm using 1
  simp only [smul_eq_mul]
  ring

theorem integral_upper_of_pointwise_margin {f g : ℝ → ℝ} {l r margin : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hpoint : ∀ t ∈ Ioo l r, f t ≤ g t + margin) :
    (∫ t in l..r, f t) ≤ (∫ t in l..r, g t) + margin * (r - l) := by
  have hc : IntervalIntegrable (fun _ : ℝ => margin) volume l r := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hlr hf (hg.add hc) hpoint
  rw [intervalIntegral.integral_add hg hc, intervalIntegral.integral_const] at hm
  convert hm using 1
  simp only [smul_eq_mul]
  ring

@[expose] noncomputable def normalizedPolynomialValue (cs : List ℚ)
    (center radius : ℚ) (t : ℝ) : ℝ :=
  polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ))

theorem normalizedPolynomialValue_continuous (cs : List ℚ) (center radius : ℚ) :
    Continuous (normalizedPolynomialValue cs center radius) := by
  exact (polynomialValue_continuous cs).comp
    ((continuous_id.sub continuous_const).div_const (radius : ℝ))

@[expose] noncomputable def leafPolynomialMinorant (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 : ℚ)
    (t : ℝ) : ℝ :=
  ((alphaA : ℝ) + (betaA : ℝ) * t) * normalizedPolynomialValue csA centerA radiusA t +
    ((alphaB : ℝ) + (betaB : ℝ) * t) * normalizedPolynomialValue csB centerB radiusB t +
      ((alpha0 : ℝ) + (beta0 : ℝ) * t)

@[expose] def leafPolynomialIntegralRat (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r : ℚ) : ℚ :=
  normalizedPolynomialIntegralRat csA alphaA betaA centerA radiusA l r +
    normalizedPolynomialIntegralRat csB alphaB betaB centerB radiusB l r +
      affinePolynomialIntegralRat [1] alpha0 beta0 l r

theorem leafPolynomialMinorant_continuous (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 : ℚ) :
    Continuous (leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
      alphaA betaA alphaB betaB alpha0 beta0) := by
  have hA : Continuous (fun t : ℝ => (alphaA : ℝ) + (betaA : ℝ) * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hB : Continuous (fun t : ℝ => (alphaB : ℝ) + (betaB : ℝ) * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have h0 : Continuous (fun t : ℝ => (alpha0 : ℝ) + (beta0 : ℝ) * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  exact ((hA.mul (normalizedPolynomialValue_continuous csA centerA radiusA)).add
    (hB.mul (normalizedPolynomialValue_continuous csB centerB radiusB))).add h0

/-- The rational return is the exact integral, including independent and
possibly negative normalizing radii for the reflected polynomial. -/
theorem integral_leafPolynomialMinorant (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r : ℚ)
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) :
    (∫ t in (l : ℝ)..(r : ℝ), leafPolynomialMinorant csA csB
      centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 t) =
      (leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 l r : ℝ) := by
  have hA : Continuous (fun t : ℝ =>
      ((alphaA : ℝ) + (betaA : ℝ) * t) * normalizedPolynomialValue csA centerA radiusA t) :=
    (continuous_const.add (continuous_const.mul continuous_id)).mul
      (normalizedPolynomialValue_continuous csA centerA radiusA)
  have hB : Continuous (fun t : ℝ =>
      ((alphaB : ℝ) + (betaB : ℝ) * t) * normalizedPolynomialValue csB centerB radiusB t) :=
    (continuous_const.add (continuous_const.mul continuous_id)).mul
      (normalizedPolynomialValue_continuous csB centerB radiusB)
  have h0 : Continuous (fun t : ℝ => (alpha0 : ℝ) + (beta0 : ℝ) * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hiA := hA.intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hiB := hB.intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hi0 := h0.intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have he0 : (∫ t in (l : ℝ)..(r : ℝ), (alpha0 : ℝ) + (beta0 : ℝ) * t) =
      (affinePolynomialIntegralRat [1] alpha0 beta0 l r : ℝ) := by
    simpa only [polynomialValue, Rat.cast_one, mul_zero, add_zero, mul_one] using
      integral_affine_polynomialValue_rat [1] alpha0 beta0 l r
  unfold leafPolynomialMinorant
  rw [intervalIntegral.integral_add (hiA.add hiB) hi0,
    intervalIntegral.integral_add hiA hiB, he0]
  simp only [normalizedPolynomialValue]
  rw [integral_normalized_polynomialValue_rat csA alphaA betaA centerA radiusA l r hrA,
    integral_normalized_polynomialValue_rat csB alphaB betaB centerB radiusB l r hrB]
  simp only [leafPolynomialIntegralRat, Rat.cast_add]

theorem leafPolynomial_integral_lower_bound {f : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r margin : ℚ)
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r)
    (hf : IntervalIntegrable f volume (l : ℝ) (r : ℝ))
    (hpoint : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), leafPolynomialMinorant csA csB
      centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 t -
        (margin : ℝ) ≤ f t) :
    ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
      alphaA betaA alphaB betaB alpha0 beta0 l r - margin * (r - l) : ℚ) : ℝ) ≤
      ∫ t in (l : ℝ)..(r : ℝ), f t := by
  have hi := (leafPolynomialMinorant_continuous csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0).intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hm := integral_lower_of_pointwise_margin (by exact_mod_cast hlr) hf hi hpoint
  rw [integral_leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r hrA hrB] at hm
  simpa only [Rat.cast_sub, Rat.cast_mul] using hm

theorem leafPolynomial_integral_upper_bound {f : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r margin : ℚ)
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r)
    (hf : IntervalIntegrable f volume (l : ℝ) (r : ℝ))
    (hpoint : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), f t ≤ leafPolynomialMinorant csA csB
      centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 t +
        (margin : ℝ)) :
    (∫ t in (l : ℝ)..(r : ℝ), f t) ≤
      ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 l r + margin * (r - l) : ℚ) : ℝ) := by
  have hi := (leafPolynomialMinorant_continuous csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0).intervalIntegrable (μ := volume) (l : ℝ) (r : ℝ)
  have hm := integral_upper_of_pointwise_margin (by exact_mod_cast hlr) hf hi hpoint
  rw [integral_leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r hrA hrB] at hm
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul] using hm

/-- Direct continuous-leaf composition. The supplied polynomial identity
is algebraic, the two hinge majorants are pointwise scalar inequalities,
and the only true-kernel estimates are the already proved uniform errors. -/
theorem conjugate_polynomial_leaf_lower_bound
    {A B L U K V : ℝ → ℝ}
    (csA csB : List ℚ)
    (centerA radiusA centerB radiusB alphaA betaA alphaB betaB alpha0 beta0 l r delta : ℚ)
    {lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂ : ℝ}
    (hrA : radiusA ≠ 0) (hrB : radiusB ≠ 0) (hlr : l ≤ r) (hdelta : 0 ≤ delta)
    (hf : IntervalIntegrable
      (fun t => profileConjugate (max (B t) 0) (|A t| + |B t|) (L t) (U t) lam)
      volume (l : ℝ) (r : ℝ))
    (hL : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), 0 ≤ L t ∧ L t ≤ 1)
    (hU : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), 0 ≤ U t ∧ U t ≤ 1)
    (hK : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), K t = min (U t) (L t))
    (hV : ∀ t ∈ Ioo (l : ℝ) (r : ℝ), V t = U t - K t)
    (hsA : -1 ≤ sA ∧ sA ≤ 1) (hsB : -1 ≤ sB ∧ sB ≤ 1)
    (hrho : 0 ≤ rho ∧ rho ≤ 1) (hsigma : 0 ≤ sigma ∧ sigma ≤ 1)
    (h₁ : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      max (|lam| - sA * normalizedPolynomialValue csA centerA radiusA t +
        sigma * normalizedPolynomialValue csB centerB radiusB t) 0 ≤
      alpha₁ * (|lam| - sA * normalizedPolynomialValue csA centerA radiusA t +
        sigma * normalizedPolynomialValue csB centerB radiusB t) + beta₁)
    (h₂ : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      max (|lam| - sA * normalizedPolynomialValue csA centerA radiusA t -
        sB * normalizedPolynomialValue csB centerB radiusB t) 0 ≤
      alpha₂ * (|lam| - sA * normalizedPolynomialValue csA centerA radiusA t -
        sB * normalizedPolynomialValue csB centerB radiusB t) + beta₂)
    (hA : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      |A t - normalizedPolynomialValue csA centerA radiusA t| ≤ (delta : ℝ))
    (hB : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      |B t - normalizedPolynomialValue csB centerB radiusB t| ≤ (delta : ℝ))
    (hweights : ∀ t ∈ Ioo (l : ℝ) (r : ℝ),
      leafPolynomialMinorant csA csB centerA radiusA centerB radiusB
        alphaA betaA alphaB betaB alpha0 beta0 t =
      expandedMinorant (normalizedPolynomialValue csA centerA radiusA t)
        (normalizedPolynomialValue csB centerB radiusB t) (L t) (K t) (V t)
        lam sA sB rho sigma alpha₁ beta₁ alpha₂ beta₂) :
    ((leafPolynomialIntegralRat csA csB centerA radiusA centerB radiusB
      alphaA betaA alphaB betaB alpha0 beta0 l r - 2 * delta * (r - l) : ℚ) : ℝ) ≤
      ∫ t in (l : ℝ)..(r : ℝ),
        profileConjugate (max (B t) 0) (|A t| + |B t|) (L t) (U t) lam := by
  apply leafPolynomial_integral_lower_bound csA csB centerA radiusA centerB radiusB
    alphaA betaA alphaB betaB alpha0 beta0 l r (2 * delta) hrA hrB hlr hf
  intro t ht
  rw [hweights t ht]
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  exact actual_conjugate_expanded_minorant (hL t ht) (hU t ht) (hK t ht) (hV t ht)
    hsA hsB hrho hsigma (h₁ t ht) (h₂ t ht) (by exact_mod_cast hdelta) (hA t ht) (hB t ht)

/-- A finite adjacent-node partition combines independently proved lower
bounds. Integrability is local to each leaf; a separate global premise is
not required. -/
theorem adjacent_integral_lower_bound {f : ℝ → ℝ} {nodes : ℕ → ℝ}
    {bounds : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k < n, IntervalIntegrable f volume (nodes k) (nodes (k + 1)))
    (hb : ∀ k < n, bounds k ≤ ∫ t in (nodes k)..(nodes (k + 1)), f t) :
    (∑ k ∈ Finset.range n, bounds k) ≤ ∫ t in (nodes 0)..(nodes n), f t := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf]
  exact Finset.sum_le_sum (fun k hk => hb k (Finset.mem_range.mp hk))

theorem adjacent_integral_upper_bound {f : ℝ → ℝ} {nodes : ℕ → ℝ}
    {bounds : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k < n, IntervalIntegrable f volume (nodes k) (nodes (k + 1)))
    (hb : ∀ k < n, (∫ t in (nodes k)..(nodes (k + 1)), f t) ≤ bounds k) :
    (∫ t in (nodes 0)..(nodes n), f t) ≤ ∑ k ∈ Finset.range n, bounds k := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf]
  exact Finset.sum_le_sum (fun k hk => hb k (Finset.mem_range.mp hk))

theorem linked_intervals_integrable {f : ℝ → ℝ} {left right : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, IntervalIntegrable f volume (left k) (right k))
    (hchain : ∀ k < n, right k = left (k + 1)) :
    IntervalIntegrable f volume (left 0) (right n) := by
  induction n with
  | zero => exact hf 0 le_rfl
  | succ n ih =>
    have hi := ih (fun k hk => hf k (by omega)) (fun k hk => hchain k (by omega))
    rw [hchain n (by omega)] at hi
    exact hi.trans (hf (n + 1) le_rfl)

theorem sum_integral_linked_intervals {f : ℝ → ℝ} {left right : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, IntervalIntegrable f volume (left k) (right k))
    (hchain : ∀ k < n, right k = left (k + 1)) :
    (∑ k ∈ Finset.range (n + 1), ∫ t in (left k)..(right k), f t) =
      ∫ t in (left 0)..(right n), f t := by
  induction n with
  | zero => simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  | succ n ih =>
    have hf' : ∀ k ≤ n, IntervalIntegrable f volume (left k) (right k) :=
      fun k hk => hf k (by omega)
    have hc' : ∀ k < n, right k = left (k + 1) :=
      fun k hk => hchain k (by omega)
    rw [Finset.sum_range_succ, ih hf' hc']
    have hi := linked_intervals_integrable hf' hc'
    rw [hchain n (by omega)] at hi ⊢
    exact intervalIntegral.integral_add_adjacent_intervals hi (hf (n + 1) le_rfl)

theorem linked_integral_lower_bound {f : ℝ → ℝ} {left right : ℕ → ℝ}
    {bounds : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, IntervalIntegrable f volume (left k) (right k))
    (hchain : ∀ k < n, right k = left (k + 1))
    (hb : ∀ k ≤ n, bounds k ≤ ∫ t in (left k)..(right k), f t) :
    (∑ k ∈ Finset.range (n + 1), bounds k) ≤ ∫ t in (left 0)..(right n), f t := by
  rw [← sum_integral_linked_intervals hf hchain]
  exact Finset.sum_le_sum (fun k hk => hb k (by simpa using Finset.mem_range.mp hk))

theorem linked_integral_upper_bound {f : ℝ → ℝ} {left right : ℕ → ℝ}
    {bounds : ℕ → ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, IntervalIntegrable f volume (left k) (right k))
    (hchain : ∀ k < n, right k = left (k + 1))
    (hb : ∀ k ≤ n, (∫ t in (left k)..(right k), f t) ≤ bounds k) :
    (∫ t in (left 0)..(right n), f t) ≤ ∑ k ∈ Finset.range (n + 1), bounds k := by
  rw [← sum_integral_linked_intervals hf hchain]
  exact Finset.sum_le_sum (fun k hk => hb k (by simpa using Finset.mem_range.mp hk))

end
end ErdosOverlap.Numerics
