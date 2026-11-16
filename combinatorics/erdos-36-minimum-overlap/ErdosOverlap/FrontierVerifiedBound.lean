/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierCover
public import ErdosOverlap.FrontierIntegralAssembly
public import ErdosOverlap.Numerics.IntegralClaimFinal
public import ErdosOverlap.Certificate.CoarseNative6OuterBindings
public import ErdosOverlap.OuterDenominators
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorTotal
public import ErdosOverlap.Certificate.FrontierLeaves.CentralTotal
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Total
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Total

namespace ErdosOverlap.Certificate.FrontierCover
open MeasureTheory Set Numerics FrontierLeaves FrontierWitnesses
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem denominator_bound : kernelDenominator Frontier.kernel ≤ (denominatorBound : ℝ) := by
  rw [← integral_denominatorIntegrand]
  exact denominatorCertificate.full_bound (by decide +kernel)

theorem central_integral : (centralIntegralLower : ℝ) ≤ ∫ t in (0 : ℝ)..1, centralIntegrand t :=
  centralCertificate.full_bound (by decide +kernel)

theorem profile_integral04 : (profileIntegralLower04 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨4, by decide⟩ t :=
  profile04Certificate.full_bound (by decide +kernel)

theorem profile_integral05 : (profileIntegralLower05 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨5, by decide⟩ t :=
  profile05Certificate.full_bound (by decide +kernel)

theorem profile_integral06 : (profileIntegralLower06 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨6, by decide⟩ t :=
  profile06Certificate.full_bound (by decide +kernel)

theorem profile_integral07 : (profileIntegralLower07 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨7, by decide⟩ t :=
  profile07Certificate.full_bound (by decide +kernel)

theorem profile_integral08 : (profileIntegralLower08 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨8, by decide⟩ t :=
  profile08Certificate.full_bound (by decide +kernel)

theorem profile_integral09 : (profileIntegralLower09 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨9, by decide⟩ t :=
  profile09Certificate.full_bound (by decide +kernel)

theorem profile_integral10 : (profileIntegralLower10 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨10, by decide⟩ t :=
  profile10Certificate.full_bound (by decide +kernel)

theorem profile_integral11 : (profileIntegralLower11 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨11, by decide⟩ t :=
  profile11Certificate.full_bound (by decide +kernel)

theorem profile_integral12 : (profileIntegralLower12 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨12, by decide⟩ t :=
  profile12Certificate.full_bound (by decide +kernel)

theorem profile_integral13 : (profileIntegralLower13 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨13, by decide⟩ t :=
  profile13Certificate.full_bound (by decide +kernel)

theorem profile_integral14 : (profileIntegralLower14 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨14, by decide⟩ t :=
  profile14Certificate.full_bound (by decide +kernel)

theorem profile_integral15 : (profileIntegralLower15 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨15, by decide⟩ t :=
  profile15Certificate.full_bound (by decide +kernel)

theorem profile_integral16 : (profileIntegralLower16 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨16, by decide⟩ t :=
  profile16Certificate.full_bound (by decide +kernel)

theorem profile_integral17 : (profileIntegralLower17 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨17, by decide⟩ t :=
  profile17Certificate.full_bound (by decide +kernel)

theorem profile_integral18 : (profileIntegralLower18 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨18, by decide⟩ t :=
  profile18Certificate.full_bound (by decide +kernel)

theorem profile_integral19 : (profileIntegralLower19 : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand ⟨19, by decide⟩ t :=
  profile19Certificate.full_bound (by decide +kernel)

theorem nativeRows_physical : PhysicalMeanInequalities nativeRows height := by
  intro r hr
  simp only [nativeRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Frontier.centralCertificate native00 height denominatorBound centralIntegralLower
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound central_integral).physicalMeanInequality
  · exact (Frontier.profileCertificate native01 height denominatorBound profileIntegralLower11
      ⟨11, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral11).physicalMeanInequality
  · exact (Frontier.profileCertificate native02 height denominatorBound profileIntegralLower14
      ⟨14, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral14).physicalMeanInequality
  · exact (Frontier.profileCertificate native03 height denominatorBound profileIntegralLower19
      ⟨19, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral19).physicalMeanInequality
  · exact (Frontier.profileCertificate native04 height denominatorBound profileIntegralLower15
      ⟨15, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral15).physicalMeanInequality
  · exact (Frontier.profileCertificate native05 height denominatorBound profileIntegralLower18
      ⟨18, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral18).physicalMeanInequality
  · exact (Frontier.profileCertificate native06 height denominatorBound profileIntegralLower17
      ⟨17, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral17).physicalMeanInequality
  · exact (Frontier.profileCertificate native07 height denominatorBound profileIntegralLower16
      ⟨16, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral16).physicalMeanInequality
  · exact (Frontier.profileCertificate native08 height denominatorBound profileIntegralLower12
      ⟨12, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral12).physicalMeanInequality
  · exact (Frontier.profileCertificate native09 height denominatorBound profileIntegralLower10
      ⟨10, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral10).physicalMeanInequality
  · exact (Frontier.profileCertificate native10 height denominatorBound profileIntegralLower13
      ⟨13, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral13).physicalMeanInequality
  · exact (Frontier.profileCertificate native11 height denominatorBound profileIntegralLower04
      ⟨4, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral04).physicalMeanInequality
  · exact (Frontier.profileCertificate native12 height denominatorBound profileIntegralLower05
      ⟨5, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral05).physicalMeanInequality
  · exact (Frontier.profileCertificate native13 height denominatorBound profileIntegralLower06
      ⟨6, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral06).physicalMeanInequality
  · exact (Frontier.profileCertificate native14 height denominatorBound profileIntegralLower07
      ⟨7, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral07).physicalMeanInequality
  · exact (Frontier.profileCertificate native15 height denominatorBound profileIntegralLower08
      ⟨8, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral08).physicalMeanInequality
  · exact (Frontier.profileCertificate native16 height denominatorBound profileIntegralLower09
      ⟨9, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      denominator_bound profile_integral09).physicalMeanInequality

open CoarseNative6

theorem outerRowsNeedingIntegrals_physical :
    PhysicalMeanInequalities outerRowsNeedingIntegrals height := by
  intro r hr h hh hlo hhi hcap
  obtain ⟨b, hb, hloeq, hhieq, ha, hbzero, hczero, hd⟩ := neededOuterBindings_spec hr
  have hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ) := by
    rw [← hloeq, ← hhieq]
    exact ⟨hlo, hhi⟩
  have hhbound := OuterNumerics.positiveBin_cap_bound hh hcap hb hm
  simpa only [ha, hbzero, hczero, hd, Rat.cast_one, Rat.cast_zero, zero_mul,
    add_zero, Rat.cast_div, Rat.cast_ofNat] using hhbound

theorem outerRowsExcludedByCap_physical :
    PhysicalMeanInequalities outerRowsExcludedByCap height := by
  intro r hr
  apply physicalMeanInequality_of_cap_threshold (by norm_num [height])
  have hlo : (5 / 8 : ℝ) ≤ (r.lo : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).2 (outerRowsExcludedByCap_lo hr)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hthreshold : 2 * (height : ℝ) - (height : ℝ) ^ 2 < (5 / 8 : ℝ) := by
    norm_num [height]
  exact hthreshold.trans_le hlo

theorem outerRows_physical : PhysicalMeanInequalities CoarseNative6.outerRows height := by
  intro r hr
  rw [CoarseNative6.outerRows_split] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact outerRowsNeedingIntegrals_physical r hr
  · exact outerRowsExcludedByCap_physical r hr

theorem positiveRows_physical  :
    PhysicalMeanInequalities positiveRows height := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact nativeRows_physical r hr
  · exact outerRows_physical r hr

theorem not_overlapCap_of_nonneg_mean 
    {h : ℝ → ℝ} (hh : Admissible h)
    (hm : 0 ≤ profileMean (overlapProfile h)) : ¬ OverlapCap h (height : ℝ) := by
  intro hcap
  have hmhi := (abs_le.mp (profileMean_abs_le_one hh)).2
  obtain ⟨r, hr, hlo, hhi, hstrict⟩ :=
    exists_separating_row positiveRows_chain positiveRows_valid
      (profileMean (overlapProfile h)) (by simpa using hm) (by simpa using hmhi)
  have hd : (0 : ℝ) < (r.d : ℝ) :=
    (Rat.cast_pos (K := ℝ)).2 (positiveRows_valid r hr).2.1
  have hbound : r.eval (profileMean (overlapProfile h)) ≤ (height : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    exact positiveRows_physical r hr h hh hlo hhi hcap
  exact (not_lt_of_ge hbound) hstrict

theorem not_overlapCap 
    {h : ℝ → ℝ} (hh : Admissible h) : ¬ OverlapCap h (height : ℝ) := by
  intro hcap
  by_cases hm : 0 ≤ profileMean (overlapProfile h)
  · exact not_overlapCap_of_nonneg_mean hh hm hcap
  · apply not_overlapCap_of_nonneg_mean hh.complement _ hcap.complement
    rw [profileMean_complement]
    linarith

theorem peak_gt_height 
    {h : ℝ → ℝ} (hh : Admissible h) : (height : ℝ) < overlapPeak h := by
  by_contra hle
  exact not_overlapCap hh ((overlapPeak_le_iff hh _).mp (le_of_not_gt hle))

theorem height_le_relaxedConstant  :
    (height : ℝ) ≤ relaxedOverlapConstant := by
  apply le_csInf relaxedPeaks_nonempty
  rintro M ⟨h, hh, rfl⟩
  exact (peak_gt_height hh).le


end
end ErdosOverlap.Certificate.FrontierCover
