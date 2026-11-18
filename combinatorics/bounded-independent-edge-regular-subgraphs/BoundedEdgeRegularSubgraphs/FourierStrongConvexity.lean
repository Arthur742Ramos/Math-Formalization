module

public import BoundedEdgeRegularSubgraphs.FourierBox
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Strong convexity of the potential on a real Fourier box
-/

@[expose] public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The real box used near either Fourier mode. -/
def realPhaseBox (r : ℝ) : Set (α → ℝ) := {x | ∀ i, |x i| ≤ r}

omit [Fintype α] [LinearOrder α] in
theorem convex_realPhaseBox (r : ℝ) : Convex ℝ (realPhaseBox (α := α) r) := by
  intro x hx y hy a b ha hb hab i
  change |a * x i + b * y i| ≤ r
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h₁ := mul_le_mul_of_nonneg_left (hx i) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy i) hb
  linarith only [h₁, h₂, congrArg (fun t : ℝ ↦ t * r) hab]

/-- Subtracting the coordinate Gaussian potential preserves convexity on the
small box, which is the input for the marginal estimate in Lemma B.1. -/
theorem convexOn_degreeFourierPotential_sub_coordinate_sq (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (q : Edge α → Set.Icc (0 : ℝ) 1) (i : α) {l curvature r : ℝ}
    (hl : 0 ≤ l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (hcurvature : 0 ≤ curvature)
    (hcurvature' : curvature ≤ l * ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α)) / 2)
    (hr : 2 * r ≤ Real.pi / 3) :
    ConvexOn ℝ (realPhaseBox (α := α) r)
      (fun t ↦ degreeFourierPotential (edgesOutsideOverlap S) q t - curvature * t i ^ 2 / 2) := by
  let A := edgesOutsideOverlap S
  let V (t : α → ℝ) := degreeFourierPotential A q t - curvature * t i ^ 2 / 2
  let box := realPhaseBox (α := α) r
  refine ⟨convex_realPhaseBox r, ?_⟩
  intro x hx y hy a b ha hb hab
  let v (j : α) := y j - x j
  let L (s : ℝ) (j : α) := x j + s * v j
  let w (e : Edge α) := (q e : ℝ) * (1 - q e)
  let m (e : Edge α) := v e.val.1 + v e.val.2
  let u (s : ℝ) (e : Edge α) := (x e.val.1 + x e.val.2) + s * m e
  let f (s : ℝ) := V (L s)
  let f' (s : ℝ) := (∑ e ∈ A, fourierPotentialSlope (w e) (u s e) * m e) - curvature * L s i * v i
  let f'' (s : ℝ) := (∑ e ∈ A, fourierPotentialCurvature (w e) (u s e) * m e ^ 2) - curvature * v i ^ 2
  have hL (s : ℝ) : L s = (1 - s) • x + s • y := by
    funext j
    change x j + s * (y j - x j) = (1 - s) * x j + s * y j
    ring
  have hbox (s : ℝ) (hs : s ∈ Icc 0 1) : L s ∈ box := by
    rw [hL]
    exact (convex_realPhaseBox r) hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have hsum (s : ℝ) (e : Edge α) : L s e.val.1 + L s e.val.2 = u s e := by
    dsimp only [L, u, m]
    ring
  have hu (s : ℝ) (hs : s ∈ Icc 0 1) (e : Edge α) : |u s e| ≤ Real.pi / 3 := by
    rw [← hsum]
    exact (abs_add_le _ _).trans (by linarith only [(hbox s hs) e.val.1, (hbox s hs) e.val.2, hr])
  have hlinear (s : ℝ) : HasDerivAt (fun t ↦ L t i) (v i) s := by
    simpa only [L, one_mul, id_eq] using ((hasDerivAt_id s).mul_const (v i)).const_add (x i)
  have hfirst (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt f (f' s) s := by
    have hh := hasDerivAt_degreeFourierPotential_line A q x v s (fun e _ ↦ hu s hs e)
    have ht := (((hlinear s).fun_pow 2).const_mul curvature).div_const (2 : ℝ)
    have he : curvature * (↑(2 : ℕ) * L s i ^ (2 - 1 : ℕ) * v i) / 2 = curvature * L s i * v i := by
      norm_num
      ring
    change HasDerivAt (fun t ↦ degreeFourierPotential A q (L t) - curvature * L t i ^ 2 / 2)
      (f' s) s
    rw [he] at ht
    exact hh.fun_sub ht
  have hsecond (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt f' (f'' s) s := by
    have hh := hasDerivAt_degreeFourierPotential_slope_line A q x v s (fun e _ ↦ hu s hs e)
    have ht := ((hlinear s).const_mul curvature).mul_const (v i)
    change HasDerivAt (fun t ↦ (∑ e ∈ A, fourierPotentialSlope (w e) (u t e) * m e) -
      curvature * L t i * v i) (f'' s) s
    simpa only [f'', pow_two, mul_assoc] using hh.fun_sub ht
  have hnonneg (s : ℝ) (hs : s ∈ Icc 0 1) : 0 ≤ f'' s := by
    have h := degreeFourierPotential_curvature_lower S hm q (L s) v hl hq
      (fun e _ ↦ by rw [hsum]; exact hu s hs e)
    simp only [hsum] at h
    have hsum_sq : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    have h' := mul_le_mul_of_nonneg_right hcurvature'
      (Finset.sum_nonneg (s := Finset.univ) (fun j _ ↦ sq_nonneg (v j)))
    have hh := mul_le_mul_of_nonneg_left hsum_sq hcurvature
    dsimp only [f'']
    exact sub_nonneg.mpr (hh.trans (h'.trans h))
  have hcv : ConvexOn ℝ (Icc 0 1) f :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun s hs ↦ (hfirst s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hfirst s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs ↦ (hsecond s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs ↦ hnonneg s (interior_subset hs))
  have h := hcv.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have h₀ : L 0 = x := by funext j; simp [L]
  have h₁ : L 1 = y := by funext j; simp [L, v]
  have hline : L b = a • x + b • y := by
    rw [hL, show (1 : ℝ) - b = a by linarith only [hab]]
  simpa only [f, smul_eq_mul, mul_zero, mul_one, zero_add, hline, h₀, h₁, V] using h

end BoundedEdgeRegularSubgraphs
