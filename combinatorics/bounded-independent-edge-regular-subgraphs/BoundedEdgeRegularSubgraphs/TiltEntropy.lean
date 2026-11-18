module

public import BoundedEdgeRegularSubgraphs.TiltQuantitative
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Likelihood cost of centring the degrees
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The contribution of one tilted edge to the log likelihood at its tilted mean. -/
noncomputable def tiltEntropy (q : Set.Icc (0 : ℝ) 1) (u : ℝ) : ℝ :=
  u * (tiltProb q u : ℝ) - Real.log (tiltNormalizer q u)

private theorem hasDerivAt_tiltNormalizer (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    HasDerivAt (tiltNormalizer q) ((q : ℝ) * Real.exp u) u := by
  have hF : HasDerivAt (fun v ↦ (q : ℝ) * Real.exp v) ((q : ℝ) * Real.exp u) u :=
    (Real.hasDerivAt_exp u).const_mul (q : ℝ)
  change HasDerivAt ((fun _ : ℝ ↦ 1 - (q : ℝ)) + fun v ↦ (q : ℝ) * Real.exp v)
    ((q : ℝ) * Real.exp u) u
  simpa only [zero_add] using (hasDerivAt_const u (1 - (q : ℝ))).add hF

private theorem hasDerivAt_tiltEntropy (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    HasDerivAt (tiltEntropy q) (u * ((tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ)))) u := by
  have hlog : HasDerivAt (fun v ↦ Real.log (tiltNormalizer q v)) (tiltProb q u : ℝ) u :=
    (hasDerivAt_tiltNormalizer q u).log (tiltNormalizer_pos q u).ne'
  change HasDerivAt ((fun v ↦ v * (tiltProb q v : ℝ)) -
    fun v ↦ Real.log (tiltNormalizer q v)) _ u
  have h := ((hasDerivAt_id u).fun_mul (hasDerivAt_tiltProb q u)).sub hlog
  have he : (tiltProb q u : ℝ) + u * ((tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ))) -
      (tiltProb q u : ℝ) = u * ((tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ))) := by ring
  simpa only [id_eq, one_mul, he] using h

private theorem min_at_zero_of_deriv_sign (f e : ℝ → ℝ) (h : ∀ x, HasDerivAt f (x * e x) x)
    (he : ∀ x, 0 ≤ e x) (x : ℝ) : f 0 ≤ f x := by
  rcases le_total 0 x with hx | hx
  · have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
        (fun t _ ↦ (h t).continuousAt.continuousWithinAt)
        (fun t _ ↦ (h t).hasDerivWithinAt) (fun t ht ↦ by
          have ht' : t ∈ Set.Ici (0 : ℝ) := interior_subset ht
          exact mul_nonneg ht' (he t))
    exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  · have hanti : AntitoneOn f (Set.Iic (0 : ℝ)) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic _)
        (fun t _ ↦ (h t).continuousAt.continuousWithinAt)
        (fun t _ ↦ (h t).hasDerivWithinAt) (fun t ht ↦ by
          have ht' : t ∈ Set.Iic (0 : ℝ) := interior_subset ht
          exact mul_nonpos_of_nonpos_of_nonneg ht' (he t))
    exact hanti (Set.mem_Iic.mpr hx) (Set.mem_Iic.mpr le_rfl) hx

/-- The single-edge entropy is nonnegative and at most (u^2/8). -/
theorem tiltEntropy_bounds (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    0 ≤ tiltEntropy q u ∧ tiltEntropy q u ≤ u ^ 2 / 8 := by
  let w (s : ℝ) := (tiltProb q s : ℝ) * (1 - (tiltProb q s : ℝ))
  have hw (s : ℝ) : 0 ≤ w s :=
    mul_nonneg (tiltProb q s).property.1 (sub_nonneg.mpr (tiltProb q s).property.2)
  have hw' (s : ℝ) : w s ≤ 1 / 4 := by
    dsimp only [w]
    nlinarith only [sq_nonneg ((tiltProb q s : ℝ) - 1 / 2)]
  have hz : tiltEntropy q 0 = 0 := by simp [tiltEntropy, tiltNormalizer]
  constructor
  · have h := min_at_zero_of_deriv_sign (tiltEntropy q) w (hasDerivAt_tiltEntropy q) hw u
    rwa [hz] at h
  · let f (s : ℝ) := s ^ 2 / 8 - tiltEntropy q s
    have hf (s : ℝ) : HasDerivAt f (s * (1 / 4 - w s)) s := by
      have h := ((hasDerivAt_pow 2 s).div_const (8 : ℝ)).sub (hasDerivAt_tiltEntropy q s)
      have he : ((2 : ℕ) : ℝ) * s ^ (2 - 1 : ℕ) / 8 - s * w s =
          s * (1 / 4 - w s) := by norm_num; ring
      change HasDerivAt ((fun v : ℝ ↦ v ^ 2 / 8) - tiltEntropy q) _ s
      rw [← he]
      exact h
    have h := min_at_zero_of_deriv_sign f (fun s ↦ 1 / 4 - w s) hf
      (fun s ↦ sub_nonneg.mpr (hw' s)) u
    have hz' : f 0 = 0 := by simp [f, hz]
    rw [hz'] at h
    exact sub_nonneg.mp h

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- On a centred atom the log likelihood is nonnegative and its upper
bound is quadratic in the Euclidean size of the potentials. -/
theorem centered_vertexTilt_logLikelihood_bounds (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ d : α → ℝ) (h : degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) = d) :
    let K := (∑ i, θ i * d i) - logPartition q θ
    0 ≤ K ∧ K ≤ (((Fintype.card α : ℝ) - 1) / 4) * ∑ i, θ i ^ 2 := by
  intro K
  have hr : K = ∑ e : Edge α, tiltEntropy (q e) (θ e.val.1 + θ e.val.2) := by
    dsimp only [K]
    rw [← h, weighted_degree_sum]
    unfold tiltEntropy logPartition vertexTilt
    rw [Finset.sum_sub_distrib]
  rw [hr]
  constructor
  · exact Finset.sum_nonneg (fun e _ ↦ (tiltEntropy_bounds _ _).1)
  · calc
      _ ≤ ∑ e : Edge α, (θ e.val.1 + θ e.val.2) ^ 2 / 8 :=
        Finset.sum_le_sum (fun e _ ↦ (tiltEntropy_bounds _ _).2)
      _ ≤ _ := by
        rw [← Finset.sum_div, sum_edge_squares]
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := θ)
        rw [Finset.card_univ] at hh
        linarith only [hh]

end BoundedEdgeRegularSubgraphs
