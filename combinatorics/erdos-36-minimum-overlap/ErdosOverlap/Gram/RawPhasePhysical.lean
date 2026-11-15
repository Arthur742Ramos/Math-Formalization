/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.RawPhase
public import ErdosOverlap.Gram.PhaseKernelPairing

/-!
# Physical validity of an exact raw phase certificate

All covariance premises are discharged from admissibility. The final theorem
uses the shared exact phase kernel and proves its quadratic expectation bound.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open MeasureTheory Set
open scoped BigOperators

theorem RawPhaseCertificate.gammaRational_getD {N : ℕ} (c : RawPhaseCertificate N) (i : ℕ) :
    (c.gammaRational.getD i 0 : ℝ) = (c.gamma.getD i 0 : ℝ)/(c.denominator : ℝ) := by
  cases ho : c.gamma[i]? with
  | none =>
    simp [RawPhaseCertificate.gammaRational, Array.getD_eq_getD_getElem?, ho]
  | some z =>
    simp [RawPhaseCertificate.gammaRational, Array.getD_eq_getD_getElem?, ho,
      Rat.cast_div, Rat.cast_intCast]

/-- The exact signed hat functional is valid for every admissible measurable
partition, with the sharp all-mean penalty. -/
theorem RawPhaseCertificate.hat_functional_lower_bound {N : ℕ}
    (c : RawPhaseCertificate N) {h : ℝ → ℝ} (hh : Admissible h) :
    (c.lowerRational : ℝ) - ((c.eta : ℝ)/(c.denominator : ℝ)) *
        (profileMean (overlapProfile h)/(2/(N : ℝ)))^2 ≤
      ∑ k : Fin (N+1), ((c.gamma.getD k.val 0 : ℝ)/(c.denominator : ℝ)) *
        hatOverlap h (2/(N : ℝ)) ((k.val : ℝ)*(2/(N : ℝ))) := by
  let a : ℝ := 2/(N : ℝ)
  let X : Fin (N+1) → Fin (N+1) → ℝ := fun i j => covariance h a i.val j.val
  let y : Fin (N+1) → ℝ := fun k => hatOverlap h a ((k.val : ℝ)*a)
  have ha : 0 < a := c.width_pos
  have hNa : (N : ℝ)*a=2 := c.width_mul
  have hd : (0 : ℝ) < (c.denominator : ℝ) := by exact_mod_cast c.denominator_pos
  have he : (0 : ℝ) ≤ (c.eta : ℝ) := by exact_mod_cast c.eta_nonnegative
  have hdiag (i : Fin (N+1)) : 0 ≤ (c.diagonal.getD i.val 0 : ℝ)/(c.denominator : ℝ) := by
    apply div_nonneg _ hd.le
    exact_mod_cast c.diagonal_nonnegative i
  have hnu (i : Fin (N+1)) : 0 ≤ (c.nonnegative.getD i.val 0 : ℝ)/(c.denominator : ℝ) := by
    apply div_nonneg _ hd.le
    exact_mod_cast c.auxiliary_nonnegative i
  have hdiagonal (i : Fin (N+1)) : X i i ≤ diagonalBound N i := by
    unfold X diagonalBound
    split_ifs with hi
    · rcases hi with hi | hi
      · rw [hi]
        exact covariance_first_diagonal_le_third hh ha
      · rw [hi]
        exact covariance_last_diagonal_le_third hh ha hNa
    · exact covariance_diagonal_le_one hh ha i.val
  have hy (k : Fin (N+1)) : y k = gridBase N a k - (a/4)*lagTrace X k := by
    rw [lagTrace_eq_range (covariance h a) (covariance_symmetric h a)]
    exact hatOverlap_eq_covariance_explicit hh ha hNa (Nat.le_of_lt_succ k.isLt)
  have hy0 (k : Fin (N+1)) : 0 ≤ y k := hatOverlap_nonneg hh ha _
  have hx : ∀ i j, X i j = X j i := fun i j => covariance_symmetric h a i.val j.val
  have ht : ∀ t ∈ c.triangles, triangleValue t X ≤ 1 := by
    intro t ht
    exact t.covariance_bound (c.triangles_valid t ht) hh ha
  have hw : ∀ t ∈ c.triangles, 0 ≤ t.weight := by
    intro t ht
    exact (c.triangles_valid t ht).2.2.1
  have htrace := covariance_trace_nonnegative hh ha hNa _ c.matrix_nonnegative
  have hmain := phaseFunctional_of_covariance a (c.denominator : ℝ)
    ((c.eta : ℝ)/(c.denominator : ℝ))
    (1/12+(profileMean (overlapProfile h)/a)^2)
    (fun i => (c.diagonal.getD i.val 0 : ℝ)/(c.denominator : ℝ))
    (fun k => (c.gamma.getD k.val 0 : ℝ)/(c.denominator : ℝ))
    (fun k => (c.nonnegative.getD k.val 0 : ℝ)/(c.denominator : ℝ))
    (gridBase N a) (diagonalBound N) y c.triangles X hd (div_nonneg he hd.le)
    hdiag hnu hw hx htrace hdiagonal (covariance_mean_bound hh ha hNa) ht hy hy0
  unfold RawPhaseCertificate.lowerRational
  rw [phaseLowerRational_cast c.cells_pos c.denominator c.denominator_pos.ne'
    c.diagonal c.gamma c.nonnegative c.eta c.triangles]
  change _ ≤ ∑ k, (c.gamma.getD k.val 0 : ℝ)/(c.denominator : ℝ)*y k
  convert hmain using 1
  dsimp [a]
  ring

/-- The actual continuous phase kernel has the exact certified quadratic
expectation for every admissible measurable relaxed partition. -/
theorem RawPhaseCertificate.kernel_functional_lower_bound {N : ℕ}
    (c : RawPhaseCertificate N) {h : ℝ → ℝ} (hh : Admissible h) :
    (c.lowerRational : ℝ) + (c.meanCoefficient : ℝ) *
        profileMean (overlapProfile h)^2 ≤
      quartetFunctional h (phaseKernel N c.gammaRational) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt c.cells_pos
  have hd : (c.denominator : ℝ) ≠ 0 := by exact_mod_cast c.denominator_pos.ne'
  have heq : (c.meanCoefficient : ℝ) * profileMean (overlapProfile h)^2 =
      -((c.eta : ℝ)/(c.denominator : ℝ)) *
        (profileMean (overlapProfile h)/(2/(N : ℝ)))^2 := by
    simp only [RawPhaseCertificate.meanCoefficient, Rat.cast_div, Rat.cast_neg,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat]
    field_simp
    ring
  rw [heq, phaseKernel_pairing_eq_hatOverlap_sum hh c.cells_pos c.gammaRational]
  simp_rw [c.gammaRational_getD]
  convert c.hat_functional_lower_bound hh using 1
  ring

end ErdosOverlap.Gram
