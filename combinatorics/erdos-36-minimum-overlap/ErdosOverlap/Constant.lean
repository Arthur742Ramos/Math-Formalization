/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.ComplementSymmetry
public import ErdosOverlap.Certificate.Quadratic

/-!
# The actual minimum-overlap constants

The peak is the supremum of the actual overlap over all real translations.
We give equivalent two-sided interval and common-cap definitions, and define
both the relaxed density infimum and the binary-partition Erdős infimum.

The final assembly accepts any exactly verified finite mean cover and proved
physical row inequalities. A quantitative even-kernel certificate supplies
one method of deriving a row; signed kernels may supply others. No physical
numerical rows are instantiated here, and no assertion is made that the
pending integral enclosures have been verified.

The auxiliary height provides a uniform non-strict lower bound on the
infimum. Its strict gap above the headline yields the strict headline bound
without assuming that an optimal partition exists.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- All values of the two signed overlaps on their physical interval. -/
def overlapValues (h : ℝ → ℝ) : Set ℝ :=
  positiveOverlap h '' Icc (0 : ℝ) 2 ∪ negativeOverlap h '' Icc (0 : ℝ) 2

/-- The maximal overlap, defined by a supremum without assuming attainment. -/
def overlapPeak (h : ℝ → ℝ) : ℝ := sSup (overlapValues h)

theorem overlapValues_nonempty (h : ℝ → ℝ) : (overlapValues h).Nonempty :=
  ⟨positiveOverlap h 0, Or.inl ⟨0, by norm_num, rfl⟩⟩

/-- The interval formulation contains exactly the whole-line correlation
values, including the zero value outside its support. -/
theorem overlapValues_eq_range_wholeOverlap (h : ℝ → ℝ) :
    overlapValues h = Set.range (wholeOverlap h) := by
  ext y
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, wholeOverlap_eq_positive h ht⟩
    · exact ⟨-t, wholeOverlap_neg_eq_negative h ht⟩
  · rintro ⟨t, rfl⟩
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · by_cases hpos : 0 ≤ t
      · exact Or.inl ⟨t, ⟨hpos, ht.2⟩, (wholeOverlap_eq_positive h ⟨hpos, ht.2⟩).symm⟩
      · have hn : -t ∈ Icc (0 : ℝ) 2 := ⟨by linarith, by linarith [ht.1]⟩
        refine Or.inr ⟨-t, hn, ?_⟩
        simpa only [neg_neg] using (wholeOverlap_neg_eq_negative h hn).symm
    · rw [wholeOverlap_eq_zero_off_support h ht]
      exact Or.inl ⟨2, by norm_num, by simp [positiveOverlap]⟩

theorem overlapPeak_eq_sSup_range (h : ℝ → ℝ) :
    overlapPeak h = sSup (Set.range (wholeOverlap h)) := by
  rw [overlapPeak, overlapValues_eq_range_wholeOverlap]

theorem positiveOverlap_le_one {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : positiveOverlap h t ≤ 1 := by
  have hi := hh.intervalIntegrable (a := 0) (b := 2-t)
    (by norm_num) (by linarith [ht.2]) (by linarith [ht.1])
  have hj := hh.intervalIntegrable (a := 2-t) (b := 2)
    (by linarith [ht.2]) (by linarith [ht.1]) le_rfl
  have hmono : positiveOverlap h t ≤ ∫ x in (0 : ℝ)..(2-t), h x := by
    apply intervalIntegral.integral_mono_on (by linarith [ht.2])
      (hh.positiveIntegrable ht) hi
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
    have hxt : x+t ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
    nlinarith [mul_nonneg (hh.nonneg x hx') (hh.nonneg (x+t) hxt)]
  have htail : 0 ≤ ∫ x in (2-t)..(2 : ℝ), h x := by
    apply intervalIntegral.integral_nonneg (by linarith [ht.1])
    intro x hx
    exact hh.nonneg x ⟨by linarith [hx.1, ht.2], hx.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi hj
  rw [hh.mass] at hadd
  linarith

theorem negativeOverlap_le_one {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : negativeOverlap h t ≤ 1 := by
  rw [← positiveOverlap_complement]
  exact positiveOverlap_le_one hh.complement ht

theorem overlapValues_bddAbove {h : ℝ → ℝ} (hh : Admissible h) :
    BddAbove (overlapValues h) := by
  refine ⟨1, ?_⟩
  rintro y (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact positiveOverlap_le_one hh ht
  · exact negativeOverlap_le_one hh ht

/-- A real number bounds the actual supremum precisely when it is a common
cap for both physical signed overlaps. -/
theorem overlapPeak_le_iff {h : ℝ → ℝ} (hh : Admissible h) (M : ℝ) :
    overlapPeak h ≤ M ↔ OverlapCap h M := by
  constructor
  · intro hM t ht
    constructor
    · exact (le_csSup (overlapValues_bddAbove hh) (Or.inl ⟨t, ht, rfl⟩)).trans hM
    · exact (le_csSup (overlapValues_bddAbove hh) (Or.inr ⟨t, ht, rfl⟩)).trans hM
  · intro hcap
    apply csSup_le (overlapValues_nonempty h)
    rintro y (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact (hcap t ht).1
    · exact (hcap t ht).2

theorem overlapPeak_is_cap {h : ℝ → ℝ} (hh : Admissible h) :
    OverlapCap h (overlapPeak h) := (overlapPeak_le_iff hh _).mp le_rfl

theorem overlapPeak_nonneg {h : ℝ → ℝ} (hh : Admissible h) : 0 ≤ overlapPeak h :=
  (overlapPeak_is_cap hh).nonneg hh

theorem overlapPeak_le_one {h : ℝ → ℝ} (hh : Admissible h) : overlapPeak h ≤ 1 := by
  apply (overlapPeak_le_iff hh _).mpr
  intro t ht
  exact ⟨positiveOverlap_le_one hh ht, negativeOverlap_le_one hh ht⟩

theorem admissible_half : Admissible (fun _ : ℝ => (1 : ℝ)/2) where
  measurable := measurable_const
  nonneg := by intro x hx; norm_num
  le_one := by intro x hx; norm_num
  mass := by simp

/-- The peaks of all measurable relaxed equal-mass densities. -/
def relaxedPeaks : Set ℝ := {M | ∃ h : ℝ → ℝ, Admissible h ∧ overlapPeak h = M}

def relaxedOverlapConstant : ℝ := sInf relaxedPeaks

theorem relaxedPeaks_nonempty : relaxedPeaks.Nonempty :=
  ⟨overlapPeak (fun _ => (1 : ℝ)/2), _, admissible_half, rfl⟩

theorem relaxedPeaks_bddBelow : BddBelow relaxedPeaks := by
  refine ⟨0, ?_⟩
  rintro M ⟨h, hh, rfl⟩
  exact overlapPeak_nonneg hh

theorem relaxedOverlapConstant_nonneg : 0 ≤ relaxedOverlapConstant := by
  apply le_csInf relaxedPeaks_nonempty
  rintro M ⟨h, hh, rfl⟩
  exact overlapPeak_nonneg hh

theorem relaxedOverlapConstant_le_one : relaxedOverlapConstant ≤ 1 := by
  exact (csInf_le relaxedPeaks_bddBelow
    (show overlapPeak (fun _ => (1 : ℝ)/2) ∈ relaxedPeaks from
      ⟨_, admissible_half, rfl⟩)).trans (overlapPeak_le_one admissible_half)

/-- A measurable partition encoded by a binary density on `[0,2]`. -/
def BinaryAdmissible (h : ℝ → ℝ) : Prop :=
  Admissible h ∧ ∀ x ∈ Icc (0 : ℝ) 2, h x = 0 ∨ h x = 1

/-- One explicit equal-mass partition, used only to establish nonemptiness. -/
def halfPartition : ℝ → ℝ := (Iic (1 : ℝ)).indicator (fun _ => 1)

theorem halfPartition_binaryAdmissible : BinaryAdmissible halfPartition := by
  have hb (x : ℝ) : halfPartition x = 0 ∨ halfPartition x = 1 := by
    by_cases hx : x ≤ 1 <;> simp [halfPartition, hx]
  constructor
  · constructor
    · exact measurable_const.indicator measurableSet_Iic
    · intro x hx
      rcases hb x with h | h <;> simp [h]
    · intro x hx
      rcases hb x with h | h <;> simp [h]
    · change (∫ x in (0 : ℝ)..2, (Iic (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) x) = 1
      calc
        _ = ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by
          simpa only [Iic_def] using
            (intervalIntegral.integral_indicator (f := fun _ : ℝ => (1 : ℝ))
              (μ := volume) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 2))
        _ = 1 := by simp
  · intro x hx
    exact hb x

def partitionPeaks : Set ℝ :=
  {M | ∃ h : ℝ → ℝ, BinaryAdmissible h ∧ overlapPeak h = M}

/-- Erdős' minimum-overlap constant for measurable equal-mass binary
partitions, in the interval-length-two normalization used in this project. -/
def erdosOverlapConstant : ℝ := sInf partitionPeaks

theorem partitionPeaks_nonempty : partitionPeaks.Nonempty :=
  ⟨overlapPeak halfPartition, halfPartition, halfPartition_binaryAdmissible, rfl⟩

theorem partitionPeaks_subset_relaxedPeaks : partitionPeaks ⊆ relaxedPeaks := by
  rintro M ⟨h, hh, heq⟩
  exact ⟨h, hh.1, heq⟩

theorem partitionPeaks_bddBelow : BddBelow partitionPeaks :=
  relaxedPeaks_bddBelow.mono partitionPeaks_subset_relaxedPeaks

/-- A universal relaxed-density lower bound also bounds every binary
partition; equality of the two infima is not assumed. -/
theorem relaxedOverlapConstant_le_erdosOverlapConstant :
    relaxedOverlapConstant ≤ erdosOverlapConstant := by
  apply le_csInf partitionPeaks_nonempty
  intro M hM
  exact csInf_le relaxedPeaks_bddBelow (partitionPeaks_subset_relaxedPeaks hM)

theorem erdosOverlapConstant_nonneg : 0 ≤ erdosOverlapConstant :=
  relaxedOverlapConstant_nonneg.trans relaxedOverlapConstant_le_erdosOverlapConstant

theorem erdosOverlapConstant_le_one : erdosOverlapConstant ≤ 1 := by
  exact (csInf_le partitionPeaks_bddBelow
    (show overlapPeak halfPartition ∈ partitionPeaks from
      ⟨halfPartition, halfPartition_binaryAdmissible, rfl⟩)).trans
    (overlapPeak_le_one halfPartition_binaryAdmissible.1)

/-- An explicit physical kernel/profile certificate for a rational mean row.
The expectation, integrability and quantitative integral inequalities must be
proved separately for the supplied kernel and witness. In particular, a JSON
success flag is not a value of this structure. -/
structure MeanKernelCertificate (r : Certificate.Row) (height : ℝ) where
  kernel : ℝ → ℝ
  witness : ℝ → ℝ
  auxiliaryLevel : ℝ
  boxCap : ℝ
  tau : ℝ
  lowerExpectation : ℝ → ℝ
  auxiliary_le_height : auxiliaryLevel ≤ height
  height_le_boxCap : height ≤ boxCap
  height_nonneg : 0 ≤ height
  denominator_pos : 0 < (r.d : ℝ)
  denominator_upper : kernelDenominator kernel ≤ (r.d : ℝ)
  witness_ac : AbsolutelyContinuousOnInterval witness 0 1
  witness_end : witness 1 = 0
  positive_integrable : IntervalIntegrable
    (fun t => max (kernel t) 0 + max (kernel (2-t)) 0) volume 0 1
  conjugate_integrable : IntervalIntegrable
    (kernelConjugate kernel auxiliaryLevel boxCap tau witness) volume 0 1
  quartet_integrable : ∀ h : ℝ → ℝ, Admissible h →
    IntervalIntegrable (quartetIntegrand h kernel) volume 0 1
  cost_integrable : ∀ h : ℝ → ℝ, Admissible h →
    IntervalIntegrable (kernelCost h kernel auxiliaryLevel) volume 0 1
  expectation_bound : ∀ h : ℝ → ℝ, Admissible h →
    lowerExpectation (profileMean (overlapProfile h)) ≤ quartetFunctional h kernel
  quantitative_return : ∀ m : ℝ, (r.lo : ℝ) ≤ m → m ≤ (r.hi : ℝ) →
    (r.a : ℝ) + (r.b : ℝ)*m + (r.c : ℝ)*m^2 ≤
      lowerExpectation m + tau*m - (∫ t in (0 : ℝ)..1, |witness t|) +
        (∫ t in (0 : ℝ)..1,
          kernelConjugate kernel auxiliaryLevel boxCap tau witness t)

theorem MeanKernelCertificate.return_le_height_of_cap
    {r : Certificate.Row} {height : ℝ} (c : MeanKernelCertificate r height)
    {h : ℝ → ℝ} (hh : Admissible h) (hcap : OverlapCap h height)
    (hlo : (r.lo : ℝ) ≤ profileMean (overlapProfile h))
    (hhi : profileMean (overlapProfile h) ≤ (r.hi : ℝ)) :
    r.eval (profileMean (overlapProfile h)) ≤ height := by
  have hphysical := kernel_profile_lower_bound hh hcap
    c.auxiliary_le_height c.height_le_boxCap c.witness_ac c.witness_end
    (c.quartet_integrable h hh) (c.cost_integrable h hh) c.positive_integrable
    c.conjugate_integrable (c.expectation_bound h hh)
  have hquant := c.quantitative_return (profileMean (overlapProfile h)) hlo hhi
  apply (div_le_iff₀ c.denominator_pos).mpr
  exact (hquant.trans hphysical).trans
    (mul_le_mul_of_nonneg_left c.denominator_upper c.height_nonneg)

/-- A quantitative row inequality for actual physical overlaps. This is an
assembly interface, not a numerical assertion. A row may be proved from an
even quartet certificate or from a signed whole-line kernel argument. -/
def PhysicalMeanInequality (r : Certificate.Row) (height : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, Admissible h →
    (r.lo : ℝ) ≤ profileMean (overlapProfile h) →
    profileMean (overlapProfile h) ≤ (r.hi : ℝ) →
    OverlapCap h height →
    (r.a : ℝ) + (r.b : ℝ)*profileMean (overlapProfile h) +
      (r.c : ℝ)*profileMean (overlapProfile h)^2 ≤ height*(r.d : ℝ)

/-- Exact reflection of a rational mean row. -/
def Certificate.Row.reflected (r : Certificate.Row) : Certificate.Row where
  lo := -r.hi
  hi := -r.lo
  a := r.a
  b := -r.b
  c := r.c
  d := r.d

theorem Certificate.Row.reflected_valid {r : Certificate.Row} {height : ℚ}
    (hr : r.Valid height) : r.reflected.Valid height := by
  rcases hr with ⟨horder, hd, hc, hlo, hhi⟩
  refine ⟨neg_le_neg horder, hd, hc, ?_, ?_⟩
  · simpa only [Certificate.Row.reflected, neg_mul_neg, neg_sq] using hhi
  · simpa only [Certificate.Row.reflected, neg_mul_neg, neg_sq] using hlo

/-- Swapping the two colours proves the reflected mean row. This applies
equally to signed and even kernels and avoids duplicate negative-mean
numerical integration. -/
theorem PhysicalMeanInequality.reflected {r : Certificate.Row} {height : ℝ}
    (hr : PhysicalMeanInequality r height) : PhysicalMeanInequality r.reflected height := by
  intro h hh hlo hhi hcap
  dsimp only [Certificate.Row.reflected] at hlo hhi ⊢
  simp only [Rat.cast_neg] at hlo hhi ⊢
  have hbound := hr (fun x => 1-h x) hh.complement
    (by rw [profileMean_complement]; linarith)
    (by rw [profileMean_complement]; linarith) hcap.complement
  rw [profileMean_complement] at hbound
  convert hbound using 1
  ring

theorem MeanKernelCertificate.physicalMeanInequality
    {r : Certificate.Row} {height : ℝ} (c : MeanKernelCertificate r height) :
    PhysicalMeanInequality r height := by
  intro h hh hlo hhi hcap
  exact (div_le_iff₀ c.denominator_pos).mp
    (c.return_le_height_of_cap hh hcap hlo hhi)

/-- Every row inequality in this interface must be independently proved for
the actual overlap functions. In particular this proposition is not supplied
by importing a list of numerical bounds. -/
def PhysicalMeanInequalities (rows : List Certificate.Row) (height : ℚ) : Prop :=
  ∀ r ∈ rows, PhysicalMeanInequality r (height : ℝ)

/-- Generic finite-cover assembly. The row list may use any rigorously proved
rounding of its numerator and denominator, and may mix signed whole-line
and even quartet arguments. -/
theorem not_overlapCap_of_physicalMeanCover
    {rows : List Certificate.Row} {height : ℚ}
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height)
    {h : ℝ → ℝ} (hh : Admissible h) : ¬ OverlapCap h (height : ℝ) := by
  intro hcap
  have hm := abs_le.mp (profileMean_abs_le_one hh)
  rcases Certificate.exists_separating_row chain valid (profileMean (overlapProfile h))
      (by simpa using hm.1) (by simpa using hm.2) with
    ⟨r, hr, hlo, hhi, hstrict⟩
  have hd : (0 : ℝ) < (r.d : ℝ) := (Rat.cast_pos (K := ℝ)).2 (valid r hr).2.1
  have hbound : r.eval (profileMean (overlapProfile h)) ≤ (height : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    exact inequalities r hr h hh hlo hhi hcap
  exact (not_lt_of_ge hbound) hstrict

theorem overlapPeak_gt_of_physicalMeanCover
    {rows : List Certificate.Row} {height : ℚ}
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height)
    {h : ℝ → ℝ} (hh : Admissible h) : (height : ℝ) < overlapPeak h := by
  by_contra hle
  exact not_overlapCap_of_physicalMeanCover chain valid inequalities hh
    ((overlapPeak_le_iff hh _).mp (le_of_not_gt hle))

theorem overlapCap_gt_of_physicalMeanCover
    {rows : List Certificate.Row} {height : ℚ}
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height)
    {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h) (hcap : OverlapCap h M) :
    (height : ℝ) < M :=
  (overlapPeak_gt_of_physicalMeanCover chain valid inequalities hh).trans_le
    ((overlapPeak_le_iff hh M).mpr hcap)

theorem le_relaxedConstant_of_physicalMeanCover
    {rows : List Certificate.Row} {height : ℚ}
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height) :
    (height : ℝ) ≤ relaxedOverlapConstant := by
  apply le_csInf relaxedPeaks_nonempty
  rintro M ⟨h, hh, rfl⟩
  exact (overlapPeak_gt_of_physicalMeanCover chain valid inequalities hh).le

theorem le_erdosConstant_of_physicalMeanCover
    {rows : List Certificate.Row} {height : ℚ}
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height) :
    (height : ℝ) ≤ erdosOverlapConstant :=
  (le_relaxedConstant_of_physicalMeanCover chain valid inequalities).trans
    relaxedOverlapConstant_le_erdosOverlapConstant

/-- The generic final theorem uses a separate rational gap to handle
strictness at the infimum. It accepts freshly verified coarse rows. -/
theorem headline_lt_erdosConstant_of_physicalMeanCover
    {rows : List Certificate.Row} {headline height : ℚ}
    (gap : headline < height)
    (chain : Certificate.CoverChain (-1) 1 rows)
    (valid : ∀ r ∈ rows, r.Valid height)
    (inequalities : PhysicalMeanInequalities rows height) :
    (headline : ℝ) < erdosOverlapConstant :=
  ((Rat.cast_lt (K := ℝ)).2 gap).trans_le
    (le_erdosConstant_of_physicalMeanCover chain valid inequalities)

end
end ErdosOverlap
