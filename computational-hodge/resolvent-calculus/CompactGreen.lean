module
public import Green
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Sequences
@[expose] public section
namespace ComputationalHodge.CompactGreen
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Filter Function Topology
open scoped Topology NNReal unitInterval ContDiff UniformConvergence

/-- The actual closed forcing ball for the inherited C0 supremum norm. -/
def forcingBall (ρ : RegularDensity) (B : ℝ) : Set (Compatible ρ) := {f | ‖f‖≤B}
/-- Actual Green images as continuous circle coefficients. -/
noncomputable def coefficientImage (ρ : RegularDensity) (B : ℝ) : Set Coefficient :=
  (fun f : Compatible ρ => (greenMap ρ f).val) '' forcingBall ρ B
noncomputable def valueBound (ρ : RegularDensity) (B : ℝ) : ℝ := 4*(mean ρ.val.val)^2*max 0 B
noncomputable def slopeBound (ρ : RegularDensity) (B : ℝ) : ℝ≥0 :=
  ⟨2*mean ρ.val.val*‖ρ.val.val‖*max 0 B,by have hm := (mean_pos ρ.val).le;positivity⟩

theorem image_value_bound (ρ : RegularDensity) (B : ℝ) {g : Coefficient}
    (hg : g∈coefficientImage ρ B) : ‖g‖≤valueBound ρ B := by
  obtain ⟨f,hf,rfl⟩:=hg
  exact (greenMap_bound ρ f).trans (mul_le_mul_of_nonneg_left
    (hf.trans (le_max_right 0 B)) (by positivity))

theorem cover_derivative_bound (ρ : RegularDensity) (B : ℝ) (f : forcingBall ρ B) (x : ℝ) :
    ‖deriv (cover (greenMap ρ f.val).val) x‖≤slopeBound ρ B := ((gradient (solution ρ f.val)).norm_coe_le_norm (x:CircleHodge.Circle)).trans ((greenMap_gradient_bound ρ f.val).trans
    (mul_le_mul_of_nonneg_left (f.property.trans (le_max_right 0 B))
      (mul_nonneg (mul_nonneg (by norm_num) (mean_pos ρ.val).le) (norm_nonneg ρ.val.val))))

theorem green_cover_lipschitz (ρ : RegularDensity) (B : ℝ) (f : forcingBall ρ B) :
    LipschitzWith (slopeBound ρ B) (cover (greenMap ρ f.val).val) :=
  lipschitzWith_of_nnnorm_deriv_le
    (fun x => (contDiff_one_iff_deriv.mp (c2_c1 (solution ρ f.val))).1 x)
    (cover_derivative_bound ρ B f)

theorem image_cover_equicontinuous (ρ : RegularDensity) (B : ℝ) :
    Equicontinuous (fun g : coefficientImage ρ B => cover g.val) := by
  apply Metric.equicontinuous_of_continuity_modulus
    (fun d : ℝ => (slopeBound ρ B : ℝ)*d)
    (by simpa only [id_eq,mul_zero] using (continuous_id.const_mul (slopeBound ρ B : ℝ)).tendsto (0 : ℝ))
  intro x y g
  obtain ⟨g,u,hu,rfl⟩:=g
  exact (green_cover_lipschitz ρ B ⟨u,hu⟩).dist_le_mul x y

theorem image_equicontinuous (ρ : RegularDensity) (B : ℝ) :
    Equicontinuous (fun g : coefficientImage ρ B => (g.val : CircleHodge.Circle → ℝ)) := equicontinuous_iff_continuous.mpr (isQuotientMap_quotient_mk'.continuous_iff.mpr
  (equicontinuous_iff_continuous.mp (image_cover_equicontinuous ρ B)))

theorem coefficient_ascoli (S : Set Coefficient) (C : ℝ)
    (hb : ∀ g∈S,‖g‖≤C) (he : Equicontinuous (fun g : S => (g.val : CircleHodge.Circle → ℝ))) :
    IsCompact (closure S) := by
  let e : Coefficient ≃ₜ BoundedContinuousFunction CircleHodge.Circle ℝ :=
    (ContinuousMap.equivBoundedOfCompact CircleHodge.Circle ℝ).toHomeomorphOfIsInducing
      (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact CircleHodge.Circle ℝ).isInducing
  let pull : (e '' S) → S := (e.toEquiv.image S).symm
  have hA : IsCompact (closure (e '' S)) := BoundedContinuousFunction.arzela_ascoli
    (Icc (-C) C) isCompact_Icc (e '' S)
    (fun f x hf => by
      obtain ⟨g,hg,rfl⟩:=hf
      change -C≤g x ∧ g x≤C
      exact abs_le.mp (by simpa only [Real.norm_eq_abs] using (g.norm_coe_le_norm x).trans (hb g hg)))
    (he.comp pull)
  exact (e.isClosedEmbedding.isCompact_preimage hA).closure_of_subset
    (fun g hg => subset_closure ⟨g,hg,rfl⟩)

theorem coefficientImage_precompact (ρ : RegularDensity) (B : ℝ) :
    IsCompact (closure (coefficientImage ρ B)) :=
  coefficient_ascoli _ (valueBound ρ B) (fun _ hg => image_value_bound ρ B hg) (image_equicontinuous ρ B)

/-- Bounded forcing gives a relatively compact family of actual Green solutions in H. -/
theorem green_ball_precompact (ρ : RegularDensity) (B : ℝ) :
    IsCompact (closure (greenMap ρ '' forcingBall ρ B)) := ((compatible_closed ρ).isClosedEmbedding_subtypeVal.isCompact_preimage
  (coefficientImage_precompact ρ B)).closure_of_subset
    (by rintro g ⟨f,hf,rfl⟩;exact subset_closure ⟨f,hf,rfl⟩)

theorem green_isCompactOperator (ρ : RegularDensity) : IsCompactOperator (greenMap ρ) := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (greenMap ρ)).mpr
  ⟨forcingBall ρ 1,(show forcingBall ρ 1=Metric.closedBall (0 : Compatible ρ) 1 from
    Set.ext (fun f => by rw [Metric.mem_closedBall,dist_zero_right];rfl)).symm ▸
      Metric.closedBall_mem_nhds _ zero_lt_one,green_ball_precompact ρ 1⟩

end ComputationalHodge.CompactGreen
