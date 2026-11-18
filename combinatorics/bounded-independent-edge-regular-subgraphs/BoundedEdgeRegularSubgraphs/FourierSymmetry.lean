module

public import BoundedEdgeRegularSubgraphs.Fourier
import Mathlib.Tactic.Ring

/-!
# The half-period shift

A simultaneous shift by π leaves the centred integrand unchanged on
the even degree lattice, as used in the proof of Theorem B.2.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α]

private theorem fourier_phase_add (n : ℤ) (t u : PhaseCircle) :
    fourier n (t + u) = fourier n t * fourier n u := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

private theorem fourier_sum_phase {ι : Type*} (s : Finset ι) (r : ι → ℤ) (x : PhaseCircle) :
    (∏ i ∈ s, fourier (r i) x) = fourier (∑ i ∈ s, r i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, fourier_add, ih]

private theorem fourier_pi_of_even (n : ℤ) (hn : Even n) :
    fourier n (Real.pi : PhaseCircle) = 1 := by
  have hπ : (Real.pi : PhaseCircle) + (Real.pi : PhaseCircle) = 0 := by
    rw [← AddCircle.coe_add, ← two_mul, AddCircle.coe_period]
  obtain ⟨m, rfl⟩ := hn
  rw [fourier_apply, add_zsmul, ← zsmul_add, hπ, smul_zero, fourier_zero']

private theorem latticeCharacter_shift_of_even (r : α → ℤ) (t : α → PhaseCircle)
    (hr : Even (∑ i, r i)) :
    latticeCharacter r (fun i ↦ t i + (Real.pi : PhaseCircle)) = latticeCharacter r t := by
  simp only [latticeCharacter, fourier_phase_add, Finset.prod_mul_distrib]
  rw [fourier_sum_phase, fourier_pi_of_even _ hr, mul_one]

variable [LinearOrder α]

/-- Simultaneous translation by π preserves the integrand for an even target degree sum. -/
theorem degreeFourier_shift_pi (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    (d : α → ℤ) (hd : Even (∑ i, d i)) (t : α → PhaseCircle) :
    degreeFourier A p d (fun i ↦ t i + (Real.pi : PhaseCircle)) = degreeFourier A p d t := by
  simp_rw [← integral_degree_character]
  refine integral_congr_ae (ae_of_all _ (fun w ↦ ?_))
  apply latticeCharacter_shift_of_even
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  exact (even_sum_degreeVector A w).sub hd

end BoundedEdgeRegularSubgraphs
