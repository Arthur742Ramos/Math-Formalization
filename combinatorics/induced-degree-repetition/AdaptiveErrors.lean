module

public import FourthMoment
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {X : Type*}

theorem large_entries (W : Finset X) (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ((W.filter fun x => t < |f x|).card:ℝ)*t^2 ≤ ∑ x ∈ W, (f x)^2 := by
  classical
  let E := W.filter fun x => t < |f x|
  have term (x) (hx : x ∈ E) : t^2 ≤ (f x)^2 := by
    rw [← sq_abs (f x)]
    exact (sq_le_sq₀ ht (abs_nonneg _)).mpr (mem_filter.mp hx).2.le
  have h := sum_le_sum (s:=E) term
  simp only [sum_const,nsmul_eq_mul] at h
  exact h.trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun _ _ _ => sq_nonneg _)

/-- A single fourth-moment bound estimates the number of exceptional rows for
every adaptively chosen retained set. -/
theorem exceptional_rows (A : X → X → ℝ) (W E : Finset X) (sub : E ⊆ W) (t b : ℝ)
    (ht : 0 ≤ t) (hb : 0 ≤ b) (mom : fourthMoment A W ≤ b^2) :
    ((W.filter fun x => t < |∑ y ∈ E, A x y|).card:ℝ)*t^2 ≤ E.card*b := by
  have h := (adaptive_subset A W E sub).trans (mul_le_mul_of_nonneg_left mom (sq_nonneg _))
  rw [← mul_pow] at h
  have val := (sq_le_sq₀ (sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hb)).mp h
  exact (large_entries W (fun x => ∑ y ∈ E, A x y) t ht).trans val

/-- A centered row sum is exactly the error in the induced degree. -/
theorem centered_degree (G : SimpleGraph X) (p : ℝ) (x : X) (E : Finset X) :
    (∑ y ∈ E, centered G p x y) = degreeOn G E x - p*E.card := by
  classical
  simp only [centered,sum_sub_distrib,sum_const,nsmul_eq_mul,sum_boole,degreeOn,mul_comm]

end InducedDegreeRepetition.Sampling
