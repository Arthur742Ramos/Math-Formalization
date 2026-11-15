/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.OuterKernel

/-! # Transparent finite checks for concrete outer kernel data -/

namespace ErdosOverlap
public section

@[expose] def OuterFrequencyData.same (r s : OuterFrequencyData) : Bool :=
  decide (r.frequency = s.frequency) && decide (r.cosineBound = s.cosineBound) &&
    decide (r.sineBound = s.sineBound)

theorem OuterFrequencyData.same_sound {r s : OuterFrequencyData} (h : r.same s = true) : r = s := by
  simp only [same, Bool.and_eq_true, decide_eq_true_eq] at h
  cases r; cases s
  simp_all

@[expose] def OuterFeature.supported (pool : List OuterFrequencyData) : OuterFeature → Bool
  | .mean | .negativeMean | .secondMoment => true
  | .cosine r | .sine r | .negativeSine r | .mixed r _ => pool.any r.same

theorem OuterFeature.valid_of_supported (pool : List OuterFrequencyData)
    (hpool : ∀ r ∈ pool, r.Valid) (feature : OuterFeature)
    (hs : feature.supported pool = true) : feature.Valid := by
  cases feature with
  | mean => trivial
  | negativeMean => trivial
  | secondMoment => trivial
  | cosine r | sine r | negativeSine r | mixed r alpha =>
    obtain ⟨s, hs, heq⟩ := List.any_eq_true.mp hs
    have heq' := OuterFrequencyData.same_sound heq
    subst s
    exact hpool r hs

@[expose] def outerTermCheck (pool : List OuterFrequencyData) (term : OuterTerm) : Bool :=
  decide (0 ≤ term.multiplier) && term.feature.supported pool

theorem outerTerms_valid_of_checks (pool : List OuterFrequencyData)
    (hpool : ∀ r ∈ pool, r.Valid) (terms : List OuterTerm)
    (hc : terms.all (outerTermCheck pool) = true) :
    ∀ term ∈ terms, 0 ≤ term.multiplier ∧ term.feature.Valid := by
  intro term ht
  have hh := List.all_eq_true.mp hc term ht
  have hparts : decide (0 ≤ term.multiplier) = true ∧ term.feature.supported pool = true := by
    simpa only [outerTermCheck, Bool.and_eq_true] using hh
  exact ⟨of_decide_eq_true hparts.1, term.feature.valid_of_supported pool hpool hparts.2⟩

structure OuterBinData where
  sourceIndex : ℕ
  lo : ℚ
  hi : ℚ
  terms : List OuterTerm
  deriving Repr

@[expose] noncomputable def OuterBinData.kernel (b : OuterBinData) : ℝ → ℝ :=
  outerKernel b.lo b.hi b.terms

@[expose] def OuterBinData.check (pool : List OuterFrequencyData) (b : OuterBinData) : Bool :=
  decide (b.lo ≤ b.hi) && b.terms.all (outerTermCheck pool)

theorem OuterBinData.expectation {h : ℝ → ℝ} (hh : Admissible h) (b : OuterBinData)
    (hm : profileMean (overlapProfile h) ∈ Set.Icc (b.lo : ℝ) (b.hi : ℝ))
    (pool : List OuterFrequencyData) (hpool : ∀ r ∈ pool, r.Valid)
    (hc : b.check pool = true) : 1 ≤ squarePairing h b.kernel := by
  apply outerKernel_expectation hh hm b.terms
  have hparts : decide (b.lo ≤ b.hi) = true ∧ b.terms.all (outerTermCheck pool) = true := by
    simpa only [OuterBinData.check, Bool.and_eq_true] using hc
  exact outerTerms_valid_of_checks pool hpool b.terms hparts.2

theorem OuterBinData.cap_bound {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h)
    (hcap : OverlapCap h M) (b : OuterBinData)
    (hm : profileMean (overlapProfile h) ∈ Set.Icc (b.lo : ℝ) (b.hi : ℝ))
    (pool : List OuterFrequencyData) (hpool : ∀ r ∈ pool, r.Valid)
    (hc : b.check pool = true) : 1 ≤ M * signedKernelDenominator b.kernel :=
  (b.expectation hh hm pool hpool hc).trans
    (squarePairing_le_cap hh hcap (outerKernel_continuous b.lo b.hi b.terms))

end
end ErdosOverlap
