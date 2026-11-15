/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.OuterTaylor

/-! # Finite coefficient checks imply continuous outer-kernel approximation -/

namespace ErdosOverlap
open Numerics MeasureTheory Set
@[expose] public section

namespace OuterFourierPolynomial

noncomputable def trigValue (p : OuterFourierPolynomial) (t : ℝ) : ℝ :=
  cosineSum p.cosineTerms t + outerSineSum p.sineTerms t

noncomputable def trigCoefficient (p : OuterFourierPolynomial)
    (center radius : ℚ) (k : ℕ) : ℝ :=
  cosineLocalCoefficientSum p.cosineTerms center radius k +
    sineLocalCoefficientSum p.sineTerms center radius k

def coefficientBox (p : OuterFourierPolynomial) (seeds : List TrigSeed)
    (radius : ℚ) (k : ℕ) : FixedBox :=
  (trigCoefficientBox p.cosineTerms false seeds radius k).add
    (trigCoefficientBox p.sineTerms true seeds radius k)

def remainderBound (p : OuterFourierPolynomial) (radius : ℚ) (n : ℕ) : ℚ :=
  cosineRemainderSum p.cosineTerms radius n + cosineRemainderSum p.sineTerms radius n

theorem coefficient_mem_box (p : OuterFourierPolynomial) {seeds : List TrigSeed}
    {center : ℚ} (hs : ∀ s ∈ seeds, s.Correct center) (radius : ℚ) (k : ℕ) :
    p.trigCoefficient center radius k ∈ p.coefficientBox seeds radius k :=
  FixedBox.mem_add (cosineCoefficientSum_mem_box p.cosineTerms hs radius k)
    (sineCoefficientSum_mem_box p.sineTerms hs radius k)

theorem localPolynomial_error (p : OuterFourierPolynomial)
    (center radius : ℚ) (n : ℕ) {u : ℝ} (hu : |u| ≤ 1) :
    |p.trigValue ((center : ℝ) + (radius : ℝ)*u) -
      ∑ k ∈ Finset.range n, p.trigCoefficient center radius k*u^k| ≤
      (p.remainderBound radius n : ℝ) := by
  have hc := cosineSum_localPolynomial_error p.cosineTerms center radius n hu
  have hs := sineSum_localPolynomial_error p.sineTerms center radius n hu
  have he : p.trigValue ((center : ℝ) + (radius : ℝ)*u) -
      ∑ k ∈ Finset.range n, p.trigCoefficient center radius k*u^k =
      (cosineSum p.cosineTerms ((center : ℝ) + (radius : ℝ)*u) -
        ∑ k ∈ Finset.range n, cosineLocalCoefficientSum p.cosineTerms center radius k*u^k) +
      (outerSineSum p.sineTerms ((center : ℝ) + (radius : ℝ)*u) -
        ∑ k ∈ Finset.range n, sineLocalCoefficientSum p.sineTerms center radius k*u^k) := by
    simp only [trigValue, trigCoefficient, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]
  simpa only [remainderBound, Rat.cast_add] using
    (abs_add_le _ _).trans (add_le_add hc hs)

def approximationCheck (p : OuterFourierPolynomial) (seeds : List TrigSeed)
    (radius : ℚ) (cs : List ℚ) (ε δ : ℚ) : Bool :=
  decide (0 ≤ ε ∧ p.remainderBound radius cs.length + (cs.length : ℚ)*ε ≤ δ) &&
    (List.range cs.length).all (fun k =>
      (p.coefficientBox seeds radius k).errorCheck (cs.getD k 0) ε)

theorem approximationCheck_sound (p : OuterFourierPolynomial) {seeds : List TrigSeed}
    {center radius : ℚ} {cs : List ℚ} {ε δ : ℚ}
    (hs : ∀ s ∈ seeds, s.Correct center)
    (hc : p.approximationCheck seeds radius cs ε δ = true) {u : ℝ} (hu : |u| ≤ 1) :
    |p.trigValue ((center : ℝ)+(radius : ℝ)*u)-polynomialValue cs u| ≤ (δ : ℝ) := by
  simp only [approximationCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  have hε : (0 : ℝ) ≤ ε := by exact_mod_cast hc.1.1
  have hbound : (p.remainderBound radius cs.length : ℝ) + (cs.length : ℝ)*(ε : ℝ) ≤ δ := by
    exact_mod_cast hc.1.2
  have hcoeff : ∀ k < cs.length,
      |p.trigCoefficient center radius k-(cs.getD k 0 : ℝ)| ≤ (ε : ℝ) := by
    intro k hk
    exact FixedBox.errorCheck_sound (p.coefficient_mem_box hs radius k)
      (hc.2 k (List.mem_range.mpr hk))
  have hp := polynomialCoefficient_sum_error cs (p.trigCoefficient center radius) hε hu hcoeff
  have ht := p.localPolynomial_error center radius cs.length hu
  exact ((abs_sub_le _ _ _).trans (add_le_add ht hp)).trans hbound

def approximation (p : OuterFourierPolynomial) (cs : List ℚ) (center radius : ℚ) : PolynomialPiece :=
  quadraticPatch cs center radius p.constant p.linear p.quadratic

theorem value_approximation_error (p : OuterFourierPolynomial) {seeds : List TrigSeed}
    {center radius : ℚ} {cs : List ℚ} {ε δ : ℚ}
    (hs : ∀ s ∈ seeds, s.Correct center)
    (hc : p.approximationCheck seeds radius cs ε δ = true) (hr : radius ≠ 0)
    {t : ℝ} (ht : |(t-(center : ℝ))/(radius : ℝ)| ≤ 1) :
    |p.value t-(p.approximation cs center radius).value t| ≤ (δ : ℝ) := by
  have h := p.approximationCheck_sound hs hc ht
  have hr' : (radius : ℝ) ≠ 0 := by exact_mod_cast hr
  have he : (center : ℝ)+(radius : ℝ)*((t-(center : ℝ))/(radius : ℝ)) = t := by
    field_simp
    ring
  rw [he] at h
  rw [approximation, quadraticPatch_value cs center radius p.constant p.linear p.quadratic hr]
  convert! h using 1
  congr 1
  unfold value trigValue
  ring

end OuterFourierPolynomial
end
end ErdosOverlap
