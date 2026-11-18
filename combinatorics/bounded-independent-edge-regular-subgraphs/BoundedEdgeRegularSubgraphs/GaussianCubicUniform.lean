module

public import BoundedEdgeRegularSubgraphs.GaussianGradientVariance
public import BoundedEdgeRegularSubgraphs.GaussianWhitenedForms
public import BoundedEdgeRegularSubgraphs.CovarianceSup
import Mathlib.Tactic

/-!
# Lemma A.2 for the full degree covariance
-/

public section

open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The cubic bounds from the variance floor and an inverse row-sum bound.
The available edges may omit an overlap clique. -/
theorem gaussianCubic_character_uniform_of_inverse_rows {l K C : ℝ}
    (hl : 0 < l) (hK : 0 < K) (hC : 0 < C) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧
      ∀ (n : ℕ), 0 < n →
      ∀ (A : Finset (Edge (Fin n)))
        (q : Edge (Fin n) → Set.Icc (0 : ℝ) 1) (a : Edge (Fin n) → ℝ),
        (∀ e ∈ A, l ≤ (q e : ℝ) * (1 - q e)) → (∀ e ∈ A, |a e| ≤ K) →
        let Q := degreeCovariance A q
        Q.PosDef → (∀ i, (∑ j, |Q⁻¹ i j|) ≤ C / (n : ℝ)) →
        let v (e : Edge (Fin n)) := (CFC.sqrt Q)⁻¹ *ᵥ realIncidence e
        let F := gaussianCubicPolynomial A a v
        let γ := standardGaussianProduct n
        let μ := ∫ x, eval x F ^ 2 ∂γ
        0 ≤ μ ∧ μ ≤ U ∧
          ‖(∫ x, realCharacter 1 (eval x F) ∂γ) - (Real.exp (-μ / 2) : ℂ)‖ ≤
            V / Real.sqrt (n : ℝ) := by
  let U := 27 * l⁻¹ * K ^ 2 * (4 * C) ^ 2
  let D := 8640 * l⁻¹ * K ^ 4 * (2 * C) ^ 2 * (4 * C) ^ 3
  let V := Real.sqrt D
  refine ⟨U, V, by dsimp only [U]; positivity, by dsimp only [V, D]; positivity, ?_⟩
  intro n hn A q a hq ha Q hQ hrow
  let k : ℝ := n
  let v (e : Edge (Fin n)) := (CFC.sqrt Q)⁻¹ *ᵥ realIncidence e
  let F := gaussianCubicPolynomial A a v
  let γ := standardGaussianProduct n
  let μ := ∫ x, eval x F ^ 2 ∂γ
  have hk₀ : 0 < k := by
    change 0 < (n : ℝ)
    exact_mod_cast hn
  have hM : (Fintype.card (Fin n) : ℝ) = k := by rw [Fintype.card_fin]
  have hframe : ∀ x : Fin n → ℝ,
      (∑ e ∈ A, ((q e : ℝ) * (1 - q e)) * (x ⬝ᵥ v e) ^ 2) = ∑ j, x j ^ 2 :=
    (whitened_degreeCovariance_frame A q hQ).1
  have heq (e f : Edge (Fin n)) : v e ⬝ᵥ v f = edgePairCovariance Q⁻¹ e f :=
    dotProduct_gaussian_whitened_edges A q hQ e f
  let w (e : Edge (Fin n)) := (q e : ℝ) * (1 - q e)
  have hv₀ : 0 ≤ 4 * C / k := by positivity
  have hv (e : Edge (Fin n)) : (∑ j, v e j ^ 2) ≤ 4 * C / k := by
    have hentry (i j : Fin n) : |Q⁻¹ i j| ≤ C / k :=
      (Finset.single_le_sum (f := fun t ↦ |Q⁻¹ i t|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)).trans (hrow i)
    have hh := (abs_edgePairCovariance_le Q⁻¹ (d := C / k) (o := C / k) le_rfl
      (fun i ↦ hentry i i) (fun i j _ ↦ hentry i j) e e).1
    have h := (le_abs_self _).trans hh
    rw [← heq] at h
    change _ ≤ 4 * C / k
    rw [mul_div_assoc]
    simpa only [dotProduct, pow_two] using h
  have hcov (e : Edge (Fin n)) : (∑ f ∈ A, |v e ⬝ᵥ v f|) ≤ 2 * C := by
    simp_rw [heq]
    refine (sum_abs_edgePairCovariance_le Q⁻¹ A e hrow).trans ?_
    rw [hM]
    apply (le_of_mul_le_mul_right (a := k)) _ hk₀
    field_simp [hk₀.ne']
    linarith only [hC]
  have hcard : (A.card : ℝ) ≤ k ^ 2 := by
    have h := Fintype.card_le_of_injective (fun e : Edge (Fin n) ↦ e.val) Subtype.val_injective
    rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h
    dsimp only [k]
    rw [← Nat.cast_pow]
    exact_mod_cast (Finset.card_le_univ A).trans h
  have hcoeff (e : Edge (Fin n)) (he : e ∈ A) : a e ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ha e he) 2
  have hU : μ ≤ U := by
    have h := integral_sq_gaussianCubicPolynomial_le A a w v hl (hq) hframe
    refine h.trans ?_
    have hh := Finset.sum_le_sum (s := A) (fun e he ↦
      mul_le_mul (hcoeff e he) (pow_le_pow_left₀
        (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v e i))) (hv e) 2) (by positivity) (by positivity))
    rw [Finset.sum_const, nsmul_eq_mul] at hh
    have hprod := mul_le_mul_of_nonneg_right hcard (show 0 ≤ K ^ 2 * (4 * C / k) ^ 2 by positivity)
    refine (mul_le_mul_of_nonneg_left (hh.trans hprod) (by positivity)).trans_eq ?_
    dsimp only [U]
    field_simp [hk₀.ne']
  have hD : Var[fun x ↦ eval x (gaussianGradientProduct F (gaussianCubicAuxiliary A a v)); γ] ≤ D / k := by
    have h := variance_gaussianCubic_gradientProduct_le A a w v hl (hq) hframe
      hK.le ha (by positivity) (fun e _ ↦ hcov e)
      hv₀ (fun e _ ↦ hv e)
    refine h.trans ?_
    have hh := mul_le_mul_of_nonneg_left hcard
      (show 0 ≤ 8640 * l⁻¹ * K ^ 4 * (2 * C) ^ 2 by positivity)
    refine (mul_le_mul_of_nonneg_right hh (show 0 ≤ (4 * C / k) ^ 3 by positivity)).trans_eq ?_
    dsimp only [D]
    field_simp [hk₀.ne']
  change 0 ≤ μ ∧ μ ≤ U ∧ ‖(∫ x, realCharacter 1 (eval x F) ∂γ) - (Real.exp (-μ / 2) : ℂ)‖ ≤ V / Real.sqrt k
  refine ⟨integral_nonneg (fun _ ↦ sq_nonneg _), hU, ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    exact (norm_integral_cubic_realCharacter_sub_gaussian_le A a v).trans
      ((Real.sqrt_le_sqrt hD).trans_eq (Real.sqrt_div (by dsimp only [D]; positivity) k))

/-- The cubic has uniformly bounded second moment, and its characteristic
function has an order-(k^{-1/2}) approximation at one. -/
theorem gaussianCubic_character_uniform {l K : ℝ} (hl : 0 < l) (hK : 0 < K) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧
      ∀ (n : ℕ), 3 ≤ n + 1 →
      ∀ (q : Edge (Fin (n + 1)) → Set.Icc (0 : ℝ) 1) (a : Edge (Fin (n + 1)) → ℝ),
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) → (∀ e, |a e| ≤ K) →
        let Q := degreeCovariance Finset.univ q
        let v (e : Edge (Fin (n + 1))) := (CFC.sqrt Q)⁻¹ *ᵥ realIncidence e
        let F := gaussianCubicPolynomial Finset.univ a v
        let γ := standardGaussianProduct (n + 1)
        let μ := ∫ x, eval x F ^ 2 ∂γ
        0 ≤ μ ∧ μ ≤ U ∧
          ‖(∫ x, realCharacter 1 (eval x F) ∂γ) - (Real.exp (-μ / 2) : ℂ)‖ ≤
            V / Real.sqrt (n + 1 : ℕ) := by
  obtain ⟨C, hC, hrows⟩ := degreeCovariance_full_inverse_rows l hl
  obtain ⟨U, V, hU, hV, h⟩ := gaussianCubic_character_uniform_of_inverse_rows hl hK hC
  refine ⟨U, V, hU, hV, ?_⟩
  intro n hn q a hq ha
  let k : ℝ := (n + 1 : ℕ)
  let A : Finset (Edge (Fin (n + 1))) := Finset.univ
  let Q := degreeCovariance A q
  have hk₃ : 3 ≤ k := by
    change (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast hn
  have hM : (Fintype.card (Fin (n + 1)) : ℝ) = k := by rw [Fintype.card_fin]
  have hHerm : Q.IsHermitian := by
    ext i j
    simp only [Q, degreeCovariance, conjTranspose_apply, star_trivial]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      contrapose! hx
      exact funext hx
    have hsum : 0 < ∑ j, x j ^ 2 := Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hh := (degreeCovariance_univ_bounds q l hl.le hq x).1
    rw [hM] at hh
    rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    exact (mul_pos (mul_pos hl (by linarith only [hk₃])) hsum).trans_le hh
  have hrow (i : Fin (n + 1)) : (∑ j, |Q⁻¹ i j|) ≤ C / k := by
    obtain ⟨_, h⟩ := hrows (α := Fin (n + 1)) (by simpa only [Fintype.card_fin] using hn) q hq
    simpa only [← hM] using h i
  exact h (n + 1) (by omega) A q a (fun e _ ↦ hq e) (fun e _ ↦ ha e) hQ hrow

end BoundedEdgeRegularSubgraphs
