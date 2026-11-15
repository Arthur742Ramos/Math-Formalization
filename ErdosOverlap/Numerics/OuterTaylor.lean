/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.SineTaylor
public import ErdosOverlap.Numerics.TaylorUniform
public import ErdosOverlap.Numerics.NativePolynomialPatch
public import ErdosOverlap.Numerics.CachedTrig
public import ErdosOverlap.OuterCompilation

/-! # Certified Taylor approximations for the signed outer kernels

The trigonometric seed table is shared by all outer kernels. Every coefficient
box is computed from the exact source weights. The generic soundness theorem
bounds the continuous function throughout a cell; sample values are never used
as a substitute for that statement.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory Set
@[expose] public section

structure TrigSeed where
  frequency : ℚ
  cosine : FixedBox
  sine : FixedBox
  deriving DecidableEq, Repr

noncomputable def TrigSeed.Correct (s : TrigSeed) (center : ℚ) : Prop :=
  Real.cos ((s.frequency * center : ℚ) : ℝ) ∈ s.cosine ∧
  Real.sin ((s.frequency * center : ℚ) : ℝ) ∈ s.sine

def TrigSeed.check (s : TrigSeed) (center : ℚ) : Bool :=
  let arg := FixedBox.ofRat (s.frequency * center)
  decide (s.cosine.lo ≤ arg.cos32.lo ∧ arg.cos32.hi ≤ s.cosine.hi ∧
    s.sine.lo ≤ arg.sin32.lo ∧ arg.sin32.hi ≤ s.sine.hi)

theorem TrigSeed.check_sound {s : TrigSeed} {center : ℚ}
    (h : s.check center = true) : s.Correct center := by
  simp only [check, decide_eq_true_eq] at h
  have hc := FixedBox.mem_cos32 (FixedBox.mem_ofRat (s.frequency * center))
  have hs := FixedBox.mem_sin32 (FixedBox.mem_ofRat (s.frequency * center))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (show (s.cosine.lo : ℝ) ≤ ((FixedBox.ofRat (s.frequency * center)).cos32.lo : ℝ) by exact_mod_cast h.1).trans hc.1
  · exact hc.2.trans (by exact_mod_cast h.2.1)
  · exact (show (s.sine.lo : ℝ) ≤ ((FixedBox.ofRat (s.frequency * center)).sin32.lo : ℝ) by exact_mod_cast h.2.2.1).trans hs.1
  · exact hs.2.trans (by exact_mod_cast h.2.2.2)

def trigSeedLookup (frequency : ℚ) : List TrigSeed → FixedBox × FixedBox
  | [] => (FixedBox.unit, FixedBox.unit)
  | s :: ss => if frequency = s.frequency then (s.cosine, s.sine)
      else trigSeedLookup frequency ss

theorem trigSeedLookup_correct {seeds : List TrigSeed} {center : ℚ}
    (hs : ∀ s ∈ seeds, s.Correct center) (frequency : ℚ) :
    Real.cos ((frequency * center : ℚ) : ℝ) ∈ (trigSeedLookup frequency seeds).1 ∧
    Real.sin ((frequency * center : ℚ) : ℝ) ∈ (trigSeedLookup frequency seeds).2 := by
  induction seeds with
  | nil =>
    exact ⟨FixedBox.mem_unit (abs_le.mp (Real.abs_cos_le_one _)),
      FixedBox.mem_unit (abs_le.mp (Real.abs_sin_le_one _))⟩
  | cons s ss ih =>
    unfold trigSeedLookup
    split_ifs with he
    · subst frequency
      exact hs s (by simp)
    · exact ih (fun q hq => hs q (by simp [hq]))

def trigCycleBox (sine : Bool) (C S : FixedBox) (k : ℕ) : FixedBox :=
  if sine then
    if k % 4 = 0 then S else if k % 4 = 1 then C
    else if k % 4 = 2 then S.neg else C.neg
  else
    if k % 4 = 0 then C else if k % 4 = 1 then S.neg
    else if k % 4 = 2 then C.neg else S

theorem cosineCycle_mem_box {C S : FixedBox} {x : ℝ}
    (hc : Real.cos x ∈ C) (hs : Real.sin x ∈ S) (k : ℕ) :
    cosineCycle k x ∈ trigCycleBox false C S k := by
  simp only [trigCycleBox, Bool.false_eq_true, ite_false, cosineCycle]
  split_ifs <;> first | exact hc | exact hs | exact FixedBox.mem_neg hc | exact FixedBox.mem_neg hs

theorem sineCycle_mem_box {C S : FixedBox} {x : ℝ}
    (hc : Real.cos x ∈ C) (hs : Real.sin x ∈ S) (k : ℕ) :
    sineCycle k x ∈ trigCycleBox true C S k := by
  simp only [trigCycleBox, ite_true, sineCycle]
  split_ifs <;> first | exact hc | exact hs | exact FixedBox.mem_neg hc | exact FixedBox.mem_neg hs

def CosineTerm.coefficientBox (a : CosineTerm) (sine : Bool)
    (seeds : List TrigSeed) (radius : ℚ) (k : ℕ) : FixedBox :=
  let CS := trigSeedLookup a.frequency seeds
  (FixedBox.ofRat (a.weight * (a.frequency * radius)^k / (k.factorial : ℚ))).mul
    (trigCycleBox sine CS.1 CS.2 k)

theorem CosineTerm.coefficient_mem_box (a : CosineTerm) {seeds : List TrigSeed}
    {center : ℚ} (hs : ∀ s ∈ seeds, s.Correct center) (radius : ℚ) (k : ℕ) :
    a.localCoefficient center radius k ∈ a.coefficientBox false seeds radius k := by
  have ht := trigSeedLookup_correct hs a.frequency
  exact FixedBox.mem_mul (FixedBox.mem_ofRat _)
    (cosineCycle_mem_box ht.1 ht.2 k)

theorem CosineTerm.sineCoefficient_mem_box (a : CosineTerm) {seeds : List TrigSeed}
    {center : ℚ} (hs : ∀ s ∈ seeds, s.Correct center) (radius : ℚ) (k : ℕ) :
    a.sineCoefficient center radius k ∈ a.coefficientBox true seeds radius k := by
  have ht := trigSeedLookup_correct hs a.frequency
  exact FixedBox.mem_mul (FixedBox.mem_ofRat _)
    (sineCycle_mem_box ht.1 ht.2 k)

noncomputable def sineLocalCoefficientSum : List CosineTerm → ℚ → ℚ → ℕ → ℝ
  | [], _, _, _ => 0
  | a :: as, c, r, k => a.sineCoefficient c r k + sineLocalCoefficientSum as c r k

def trigCoefficientBox : List CosineTerm → Bool → List TrigSeed → ℚ → ℕ → FixedBox
  | [], _, _, _, _ => FixedBox.ofRat 0
  | a :: as, sine, seeds, r, k =>
      (a.coefficientBox sine seeds r k).add (trigCoefficientBox as sine seeds r k)

theorem cosineCoefficientSum_mem_box (terms : List CosineTerm) {seeds : List TrigSeed}
    {center : ℚ} (hs : ∀ s ∈ seeds, s.Correct center) (radius : ℚ) (k : ℕ) :
    cosineLocalCoefficientSum terms center radius k ∈
      trigCoefficientBox terms false seeds radius k := by
  induction terms with
  | nil => simpa only [cosineLocalCoefficientSum, sineLocalCoefficientSum,
      trigCoefficientBox, Rat.cast_zero] using FixedBox.mem_ofRat 0
  | cons a as ih => exact FixedBox.mem_add (a.coefficient_mem_box hs radius k) ih

theorem sineCoefficientSum_mem_box (terms : List CosineTerm) {seeds : List TrigSeed}
    {center : ℚ} (hs : ∀ s ∈ seeds, s.Correct center) (radius : ℚ) (k : ℕ) :
    sineLocalCoefficientSum terms center radius k ∈
      trigCoefficientBox terms true seeds radius k := by
  induction terms with
  | nil => simpa only [cosineLocalCoefficientSum, sineLocalCoefficientSum,
      trigCoefficientBox, Rat.cast_zero] using FixedBox.mem_ofRat 0
  | cons a as ih => exact FixedBox.mem_add (a.sineCoefficient_mem_box hs radius k) ih

theorem sineSum_localPolynomial_error (terms : List CosineTerm)
    (center radius : ℚ) (n : ℕ) {u : ℝ} (hu : |u| ≤ 1) :
    |outerSineSum terms ((center : ℝ) + (radius : ℝ) * u) -
      ∑ k ∈ Finset.range n, sineLocalCoefficientSum terms center radius k * u ^ k| ≤
      (cosineRemainderSum terms radius n : ℝ) := by
  induction terms with
  | nil =>
    simp only [outerSineSum, sineLocalCoefficientSum, zero_mul, Finset.sum_const_zero,
      sub_self, abs_zero, cosineRemainderSum, Rat.cast_zero, le_refl]
  | cons term terms ih =>
    have ht := term.sinePolynomial_error center radius n hu
    have he : outerSineSum (term :: terms) ((center : ℝ) + (radius : ℝ) * u) -
        ∑ k ∈ Finset.range n, sineLocalCoefficientSum (term :: terms) center radius k * u ^ k =
        (term.sineValue ((center : ℝ) + (radius : ℝ) * u) -
          term.sinePolynomial center radius n u) +
        (outerSineSum terms ((center : ℝ) + (radius : ℝ) * u) -
          ∑ k ∈ Finset.range n, sineLocalCoefficientSum terms center radius k * u ^ k) := by
      simp only [outerSineSum, sineLocalCoefficientSum, CosineTerm.sinePolynomial,
        CosineTerm.sineValue, add_mul, Finset.sum_add_distrib]
      ring
    rw [he]
    simpa only [cosineRemainderSum, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add ht ih)

def FixedBox.errorCheck (I : FixedBox) (q ε : ℚ) : Bool :=
  I.lowerBoundedBy (q-ε) && I.upperBoundedBy (q+ε)

theorem FixedBox.errorCheck_sound {I : FixedBox} {x : ℝ} {q ε : ℚ}
    (hx : x ∈ I) (h : I.errorCheck q ε = true) : |x-(q : ℝ)| ≤ (ε : ℝ) := by
  simp only [errorCheck, Bool.and_eq_true] at h
  have hl := I.lowerBoundedBy_sound hx h.1
  have hu := I.upperBoundedBy_sound hx h.2
  simp only [Rat.cast_sub, Rat.cast_add] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end ErdosOverlap.Numerics
