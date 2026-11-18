module

public import BoundedEdgeRegularSubgraphs.DensitySurplus
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Clipping the quartic correction to the Gaussian box
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Coordinate clipping to the symmetric interval of radius `r`. -/
def clipRadius (r : ℝ) (t : ℝ) : ℝ := min r (max (-r) t)

theorem abs_clipRadius_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : |clipRadius r t| ≤ r := by
  apply abs_le.mpr
  constructor
  · exact le_min (by linarith) (le_max_left _ _)
  · exact min_le_left _ _

theorem abs_clipRadius_sub_le (r s t : ℝ) : |clipRadius r s - clipRadius r t| ≤ |s - t| := by
  unfold clipRadius
  have h := abs_min_sub_min_le_max r (max (-r) s) r (max (-r) t)
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (max (-r) s - max (-r) t))] at h
  have h' := abs_max_sub_max_le_max (-r) s (-r) t
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (s - t))] at h'
  exact h.trans h'

theorem clipRadius_eq_of_abs_le {r t : ℝ} (h : |t| ≤ r) : clipRadius r t = t := by
  unfold clipRadius
  obtain ⟨hl, hu⟩ := abs_le.mp h
  rw [max_eq_right hl, min_eq_right hu]

/-- The quartic correction on a vector of Fourier coordinates. -/
noncomputable def edgeQuartic (A : Finset (Edge α)) (b : Edge α → ℝ) (x : α → ℝ) : ℝ :=
  ∑ e ∈ A, b e * (x e.val.1 + x e.val.2) ^ 4

private theorem abs_fourth_sub_le {u v R : ℝ} (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |u ^ 4 - v ^ 4| ≤ 4 * R ^ 3 * |u - v| := by
  have hr : 0 ≤ R := (abs_nonneg u).trans hu
  have hsum : |u + v| ≤ 2 * R := (abs_add_le _ _).trans (by linarith only [hu, hv])
  have hu' := pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hv' := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hu' hv'
  have hsq : u ^ 2 + v ^ 2 ≤ 2 * R ^ 2 := by linarith only [hu', hv']
  rw [show u ^ 4 - v ^ 4 = (u - v) * (u + v) * (u ^ 2 + v ^ 2) by ring]
  simp only [abs_mul, abs_of_nonneg (add_nonneg (sq_nonneg u) (sq_nonneg v))]
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hsum (abs_nonneg (u - v))) hsq
    (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
  calc
    _ ≤ |u - v| * (2 * R) * (2 * R ^ 2) := h
    _ = _ := by ring

/-- The quartic polynomial has the stated deterministic Lipschitz
constant on the box, before composing with the Gaussian linear map. -/
theorem abs_edgeQuartic_sub_le (A : Finset (Edge α)) (b : Edge α → ℝ)
    {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hb : ∀ e ∈ A, |b e| ≤ K)
    (x y : α → ℝ) (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r) :
    |edgeQuartic A b x - edgeQuartic A b y| ≤
      4 * (2 * r) ^ 3 * K * ((Fintype.card α : ℝ) - 1) * ∑ i, |x i - y i| := by
  let z (i : α) := |x i - y i|
  let C := 4 * (2 * r) ^ 3 * K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound (e : Edge α) (he : e ∈ A) :
      |b e * (x e.val.1 + x e.val.2) ^ 4 - b e * (y e.val.1 + y e.val.2) ^ 4| ≤
        C * (z e.val.1 + z e.val.2) := by
    have h₁ : |x e.val.1 + x e.val.2| ≤ 2 * r :=
      (abs_add_le _ _).trans (by linarith only [hx e.val.1, hx e.val.2])
    have h₂ : |y e.val.1 + y e.val.2| ≤ 2 * r :=
      (abs_add_le _ _).trans (by linarith only [hy e.val.1, hy e.val.2])
    have h₃ := abs_fourth_sub_le h₁ h₂
    have h₄ : |x e.val.1 + x e.val.2 - (y e.val.1 + y e.val.2)| ≤ z e.val.1 + z e.val.2 := by
      rw [show x e.val.1 + x e.val.2 - (y e.val.1 + y e.val.2) =
        (x e.val.1 - y e.val.1) + (x e.val.2 - y e.val.2) by ring]
      exact abs_add_le _ _
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ K * (4 * (2 * r) ^ 3 * (z e.val.1 + z e.val.2)) :=
        mul_le_mul (hb e he) (h₃.trans (mul_le_mul_of_nonneg_left h₄ (by positivity)))
          (abs_nonneg _) hK
      _ = _ := by dsimp only [C]; ring
  unfold edgeQuartic
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ A, |b e * (x e.val.1 + x e.val.2) ^ 4 -
        b e * (y e.val.1 + y e.val.2) ^ 4| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ A, C * (z e.val.1 + z e.val.2) := Finset.sum_le_sum hbound
    _ ≤ ∑ e : Edge α, C * (z e.val.1 + z e.val.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ mul_nonneg hC (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = _ := by
      rw [← Finset.mul_sum, sum_edge_endpoint_values]
      dsimp only [C, z]
      ring

/-- Clipping is nonexpansive coordinatewise, and the quartic correction
has a Euclidean Lipschitz bound on the clipped linear image. -/
theorem abs_edgeQuartic_clip_linear_sub_le (A : Finset (Edge α)) (b : Edge α → ℝ)
    {K r L : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix α α ℝ)
    (hB : ∀ v : α → ℝ, (∑ i, (B *ᵥ v) i ^ 2) ≤ L ^ 2 * ∑ i, v i ^ 2)
    (x y : α → ℝ) :
    |edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i)) -
        edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ y) i))| ≤
      4 * (2 * r) ^ 3 * K * ((Fintype.card α : ℝ) - 1) *
        Real.sqrt (Fintype.card α) * L * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  classical
  by_cases hα : Nonempty α
  · let v := B *ᵥ (x - y)
    let s := ∑ i : α, (x i - y i) ^ 2
    let c := 4 * (2 * r) ^ 3 * K * ((Fintype.card α : ℝ) - 1)
    have hn : (1 : ℝ) ≤ Fintype.card α := by
      have h : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hα
      exact_mod_cast h
    have hc : 0 ≤ c := by dsimp only [c]; exact mul_nonneg (by positivity) (sub_nonneg.mpr hn)
    have hs : 0 ≤ s := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i - y i))
    have hv (i : α) : (B *ᵥ x) i - (B *ᵥ y) i = v i := by
      dsimp only [v]
      rw [Matrix.mulVec_sub]
      rfl
    have hl : (∑ i, |v i|) ≤ Real.sqrt (Fintype.card α) * L * Real.sqrt s := by
      have h₀ : (∑ i, |v i|) ^ 2 ≤ (Fintype.card α : ℝ) * ∑ i, v i ^ 2 := by
        simpa only [Finset.card_univ, sq_abs] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ |v i|))
      have h₁ := hB (x - y)
      change (∑ i, v i ^ 2) ≤ L ^ 2 * s at h₁
      apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card α), Real.sq_sqrt hs]
      have h := h₀.trans (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _))
      linarith only [h]
    have h := abs_edgeQuartic_sub_le A b hK hr hb
      (fun i ↦ clipRadius r ((B *ᵥ x) i)) (fun i ↦ clipRadius r ((B *ᵥ y) i))
      (fun i ↦ abs_clipRadius_le hr _) (fun i ↦ abs_clipRadius_le hr _)
    refine h.trans ?_
    change c * _ ≤ c * Real.sqrt (Fintype.card α) * L * Real.sqrt s
    rw [mul_assoc c, mul_assoc c]
    apply mul_le_mul_of_nonneg_left _ hc
    exact (Finset.sum_le_sum (fun i _ ↦
      (abs_clipRadius_sub_le r _ _).trans_eq (congrArg abs (hv i)))).trans hl
  · have : IsEmpty α := not_nonempty_iff.mp hα
    have hA : A = ∅ := by ext e; exact isEmptyElim e.val.1
    simp [edgeQuartic, hA, Real.sqrt_zero]

end BoundedEdgeRegularSubgraphs
