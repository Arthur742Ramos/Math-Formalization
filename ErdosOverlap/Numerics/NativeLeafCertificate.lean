/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafCapacities
public import ErdosOverlap.KernelIntegrability
public import ErdosOverlap.Native6WitnessModeFacts
public import ErdosOverlap.ZeroWitness

/-!
# Soundness of native denominator, boundary and profile integration leaves

The only approximation premise is the actual a.e. error of the two source
polynomial patches. The separate actual wrapper supplies this premise from
the proved affine compiler and uniform Taylor approximation.
-/

@[expose] public section

namespace ErdosOverlap.Native6Leaves

open Numerics MeasureTheory Set

noncomputable def Geometry.Approximation (g : Geometry) : Prop :=
  (∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
    |Native6.kernel t-g.patchA.value t| ≤ (approximationError : ℝ)) ∧
  (∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
    |Native6.kernel (2-t)-g.patchB.value t| ≤ (approximationError : ℝ))

noncomputable def profileIntegrand (mode : Fin 10) : ℝ → ℝ :=
  kernelConjugate Native6.kernel (auxiliaryLevel : ℝ) (boxCap : ℝ)
    (Native6Witnesses.modeTau mode : ℝ) (Native6Witnesses.modeWitness mode)

noncomputable def centralIntegrand (t : ℝ) : ℝ :=
  max (Native6.kernel (2-t)) 0 * max (2*(auxiliaryLevel : ℝ)-t) 0

noncomputable def denominatorIntegrand (t : ℝ) : ℝ :=
  2*(max (Native6.kernel t) 0+max (Native6.kernel (2-t)) 0)

theorem profileIntegrand_integrable (mode : Fin 10) :
    IntervalIntegrable (profileIntegrand mode) volume 0 1 :=
  Native6.conjugate_intervalIntegrable (Native6Witnesses.modeWitness_absolutelyContinuous mode)
    (auxiliaryLevel : ℝ) (boxCap : ℝ) (Native6Witnesses.modeTau mode : ℝ)

theorem centralIntegrand_integrable : IntervalIntegrable centralIntegrand volume 0 1 := by
  have h := Native6.conjugate_intervalIntegrable zeroWitness_absolutelyContinuous
    (auxiliaryLevel : ℝ) (boxCap : ℝ) 0
  have heq : kernelConjugate Native6.kernel (auxiliaryLevel : ℝ) (boxCap : ℝ) 0
      (fun _ => 0) = centralIntegrand := by
    funext t
    exact kernelConjugate_zero_witness Native6.kernel (auxiliaryLevel : ℝ) (boxCap : ℝ) t
  rw [heq] at h
  exact h

theorem denominatorIntegrand_integrable : IntervalIntegrable denominatorIntegrand volume 0 1 :=
  Native6.positivePart_intervalIntegrable.const_mul 2

theorem Geometry.intervalIntegrable {g : Geometry} (hg : g.Valid) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable f volume (g.left : ℝ) (g.right : ℝ) := by
  have hlo : (0 : ℝ) ≤ (g.left : ℝ) := (Rat.cast_nonneg (K := ℝ)).2 hg.1
  have hhi : (g.right : ℝ) ≤ 1 := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).2 hg.2.2.1
  have horder : (g.left : ℝ) ≤ (g.right : ℝ) := (Rat.cast_le (K := ℝ)).2 hg.2.1.le
  apply hf.mono_set
  rw [uIcc_of_le horder, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro t ht
  exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩

theorem Geometry.mem_unitInterval {g : Geometry} (hg : g.Valid) {t : ℝ}
    (ht : t ∈ Icc (g.left : ℝ) (g.right : ℝ)) : t ∈ Icc (0 : ℝ) 1 := by
  have hlo : (0 : ℝ) ≤ (g.left : ℝ) := (Rat.cast_nonneg (K := ℝ)).2 hg.1
  have hhi : (g.right : ℝ) ≤ 1 := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).2 hg.2.2.1
  exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩

theorem weights_continuous (w : LeafWeights) (PA PB : PolynomialPiece) :
    Continuous (fun t => w.value (PA.value t) (PB.value t) t) := by
  have ha (a : RationalAffine) : Continuous a.value :=
    continuous_const.add (continuous_const.mul continuous_id)
  exact (((ha w.weightA).mul PA.continuous).add
    ((ha w.weightB).mul PB.continuous)).add (ha w.weight0)

theorem lower_of_box_mem {I : FixedBox} {x : ℝ} {z : ℤ}
    (hx : x ∈ I) (hz : z ≤ I.lo) : (z : ℝ)/(fixedScale : ℝ) ≤ x := by
  apply (div_le_iff₀ fixedScale_real_pos).mpr
  exact (by exact_mod_cast hz : (z : ℝ) ≤ (I.lo : ℝ)).trans hx.1

theorem upper_of_box_mem {I : FixedBox} {x : ℝ} {z : ℤ}
    (hx : x ∈ I) (hz : I.hi ≤ z) : x ≤ (z : ℝ)/(fixedScale : ℝ) := by
  apply (le_div_iff₀ fixedScale_real_pos).mpr
  exact hx.2.trans (by exact_mod_cast hz : (I.hi : ℝ) ≤ (z : ℝ))

theorem approximationError_nonneg : (0 : ℝ) ≤ (approximationError : ℝ) := by
  norm_num [approximationError]

theorem ProfileLeaf.pointwise (leaf : ProfileLeaf) (mode : Fin 10)
    (hc : leaf.check mode = true) (ha : leaf.geometry.val.Approximation) :
    ∀ᵐ t ∂volume.restrict (Ioo (leaf.geometry.val.left : ℝ) (leaf.geometry.val.right : ℝ)),
      (profileWeights leaf.geometry.val leaf.lam).value
        (leaf.geometry.val.patchA.value t) (leaf.geometry.val.patchB.value t) t-
          2*(approximationError : ℝ) ≤ profileIntegrand mode t := by
  simp only [ProfileLeaf.check, Bool.and_eq_true] at hc
  have hs := Native6Witnesses.slopeLeafCheck_sound mode leaf.cell
    leaf.geometry.val.left leaf.geometry.val.right leaf.lam hc.1.2
  filter_upwards [ha.1, ha.2, hs, self_mem_ae_restrict measurableSet_Ioo] with t hA hB hlam ht
  have htc : t ∈ Icc (leaf.geometry.val.left : ℝ) (leaf.geometry.val.right : ℝ) :=
    ⟨ht.1.le, ht.2.le⟩
  have hrange := leaf.geometry.cache_correct.1 t htc
  have hcaps := capacities_bounds hc.1.1 htc (Geometry.mem_unitInterval leaf.geometry.valid htc)
  have hp := conjugateWeights_pointwise leaf.lam
    (capacities leaf.geometry.val.left leaf.geometry.val.right).L
    (capacities leaf.geometry.val.left leaf.geometry.val.right).K
    (capacities leaf.geometry.val.left leaf.geometry.val.right).V
    hrange.1 hrange.2 hcaps.1 hcaps.2 (capacities_K hc.1.1 htc)
    (capacities_V _ _ t) approximationError_nonneg hA hB
  change _ ≤ profileConjugate (max (Native6.kernel (2-t)) 0)
    (|Native6.kernel t|+|Native6.kernel (2-t)|) (max (2*(auxiliaryLevel : ℝ)-t) 0)
    (min t (boxCap : ℝ)) (dualSlope _ _ t)
  rw [hlam]
  simpa only [profileWeights, capacities_L hc.1.1 htc, capacities_U hc.1.1 htc] using hp

theorem ProfileLeaf.sound (leaf : ProfileLeaf) (mode : Fin 10)
    (hc : leaf.check mode = true) (ha : leaf.geometry.val.Approximation) :
    (leaf.lowerBound : ℝ) ≤
      ∫ t in (leaf.geometry.val.left : ℝ)..(leaf.geometry.val.right : ℝ), profileIntegrand mode t := by
  have hpoint := leaf.pointwise mode hc ha
  have hcheck := hc
  simp only [ProfileLeaf.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hb := lower_of_box_mem
    (LeafCache.weights_integral_mem leaf.geometry.cache_correct
      (profileWeights leaf.geometry.val leaf.lam))
    hcheck.2
  have hI := integral_lower_of_ae_margin
    ((Rat.cast_le (K := ℝ)).2 leaf.geometry.valid.2.1.le)
    (Geometry.intervalIntegrable leaf.geometry.valid (profileIntegrand_integrable mode))
    ((weights_continuous (profileWeights leaf.geometry.val leaf.lam)
      leaf.geometry.val.patchA leaf.geometry.val.patchB).intervalIntegrable _ _) hpoint
  simp only [ProfileLeaf.lowerBound, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_mul, Rat.cast_ofNat]
  linarith

theorem centralWeights_value (g : Geometry) (PA PB t : ℝ) :
    (centralWeights g).value PA PB t =
      (boxPositiveSelector g.cache.rangeB : ℝ)*PB*(capacities g.left g.right).L.value t := by
  simp only [centralWeights, LeafWeights.value, RationalAffine.scale, RationalAffine.value,
    Rat.cast_zero, Rat.cast_mul, Rat.cast_intCast]
  ring

theorem CentralLeaf.pointwise (leaf : CentralLeaf) (hc : leaf.check = true)
    (ha : leaf.geometry.val.Approximation) :
    ∀ᵐ t ∂volume.restrict (Ioo (leaf.geometry.val.left : ℝ) (leaf.geometry.val.right : ℝ)),
      (centralWeights leaf.geometry.val).value
        (leaf.geometry.val.patchA.value t) (leaf.geometry.val.patchB.value t) t-
          2*(approximationError : ℝ) ≤ centralIntegrand t := by
  simp only [CentralLeaf.check, Bool.and_eq_true] at hc
  filter_upwards [ha.2, self_mem_ae_restrict measurableSet_Ioo] with t hB ht
  have htc : t ∈ Icc (leaf.geometry.val.left : ℝ) (leaf.geometry.val.right : ℝ) :=
    ⟨ht.1.le, ht.2.le⟩
  have hL := (capacities_bounds hc.1 htc
    (Geometry.mem_unitInterval leaf.geometry.valid htc)).1
  have hselector := unit_mul_le_positivePart
    (x := leaf.geometry.val.patchB.value t) (boxPositiveSelector_bounds leaf.geometry.val.cache.rangeB)
  have herr : |max (leaf.geometry.val.patchB.value t) 0-max (Native6.kernel (2-t)) 0| ≤
      (approximationError : ℝ) :=
    (abs_max_sub_max_le_abs (leaf.geometry.val.patchB.value t)
      (Native6.kernel (2-t)) 0).trans (by simpa only [abs_sub_comm] using hB)
  have hb : (boxPositiveSelector leaf.geometry.val.cache.rangeB : ℝ)*
      leaf.geometry.val.patchB.value t ≤ max (Native6.kernel (2-t)) 0+(approximationError : ℝ) := by
    linarith [(abs_le.mp herr).2]
  have hm := mul_le_mul_of_nonneg_right hb hL.1
  have he := mul_le_mul_of_nonneg_left hL.2 approximationError_nonneg
  rw [centralWeights_value]
  have hLc := capacities_L hc.1 htc
  unfold centralIntegrand
  rw [← hLc]
  nlinarith [approximationError_nonneg]

theorem CentralLeaf.sound (leaf : CentralLeaf) (hc : leaf.check = true)
    (ha : leaf.geometry.val.Approximation) :
    (leaf.lowerBound : ℝ) ≤
      ∫ t in (leaf.geometry.val.left : ℝ)..(leaf.geometry.val.right : ℝ), centralIntegrand t := by
  have hpoint := leaf.pointwise hc ha
  have hcheck := hc
  simp only [CentralLeaf.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hb := lower_of_box_mem
    (LeafCache.weights_integral_mem leaf.geometry.cache_correct
      (centralWeights leaf.geometry.val)) hcheck.2
  have hI := integral_lower_of_ae_margin
    ((Rat.cast_le (K := ℝ)).2 leaf.geometry.valid.2.1.le)
    (Geometry.intervalIntegrable leaf.geometry.valid centralIntegrand_integrable)
    ((weights_continuous (centralWeights leaf.geometry.val)
      leaf.geometry.val.patchA leaf.geometry.val.patchB).intervalIntegrable _ _) hpoint
  simp only [CentralLeaf.lowerBound, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_mul, Rat.cast_ofNat]
  linarith

theorem denominatorWeights_value (g : Geometry) (PA PB t : ℝ) :
    (denominatorWeights g).value PA PB t =
      2*(g.cache.rangeA.positiveLine.value PA+g.cache.rangeB.positiveLine.value PB) := by
  simp only [denominatorWeights, LeafWeights.value, RationalAffine.value,
    Rat.cast_zero, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]
  ring

theorem DenominatorLeaf.pointwise (leaf : DenominatorLeaf)
    (ha : leaf.geometry.val.Approximation) :
    ∀ᵐ t ∂volume.restrict (Ioo (leaf.geometry.val.left : ℝ) (leaf.geometry.val.right : ℝ)),
      denominatorIntegrand t ≤ (denominatorWeights leaf.geometry.val).value
        (leaf.geometry.val.patchA.value t) (leaf.geometry.val.patchB.value t) t+
          4*(approximationError : ℝ) := by
  filter_upwards [ha.1, ha.2, self_mem_ae_restrict measurableSet_Ioo] with t hA hB ht
  have hrange := leaf.geometry.cache_correct.1 t ⟨ht.1.le, ht.2.le⟩
  have hpa := FixedBox.positiveLine_sound hrange.1
  have hpb := FixedBox.positiveLine_sound hrange.2
  have hp := denominator_upper_of_approx hA hB
    (by simpa only [RationalAffine.value, add_comm] using hpa)
    (by simpa only [RationalAffine.value, add_comm] using hpb)
  rw [denominatorWeights_value]
  change 2*(max (Native6.kernel t) 0+max (Native6.kernel (2-t)) 0) ≤ _
  convert hp using 1
  simp only [RationalAffine.value]
  ring

theorem DenominatorLeaf.sound (leaf : DenominatorLeaf) (hc : leaf.check = true)
    (ha : leaf.geometry.val.Approximation) :
    (∫ t in (leaf.geometry.val.left : ℝ)..(leaf.geometry.val.right : ℝ), denominatorIntegrand t) ≤
      (leaf.upperBound : ℝ) := by
  have hpoint := leaf.pointwise ha
  have hcheck := of_decide_eq_true hc
  have hb := upper_of_box_mem
    (LeafCache.weights_integral_mem leaf.geometry.cache_correct
      (denominatorWeights leaf.geometry.val)) hcheck
  have hI := integral_upper_of_ae_margin
    ((Rat.cast_le (K := ℝ)).2 leaf.geometry.valid.2.1.le)
    (Geometry.intervalIntegrable leaf.geometry.valid denominatorIntegrand_integrable)
    ((weights_continuous (denominatorWeights leaf.geometry.val)
      leaf.geometry.val.patchA leaf.geometry.val.patchB).intervalIntegrable _ _) hpoint
  simp only [DenominatorLeaf.upperBound, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_mul, Rat.cast_ofNat]
  linarith

end ErdosOverlap.Native6Leaves
