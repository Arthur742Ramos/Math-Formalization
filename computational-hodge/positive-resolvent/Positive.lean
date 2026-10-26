module
public import FullOperator
public import Mathlib.Analysis.Calculus.DerivativeTest
@[expose] public section
namespace ComputationalHodge.PositiveResolvent
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm ComputationalHodge.FullCircleRange
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open MeasureTheory Set Function Filter Topology
open scoped Topology NNReal unitInterval ContDiff

/-- Necessary second-derivative sign at an actual local minimum. -/
theorem second_derivative_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hx := isLocalMax_of_deriv_deriv_neg (lt_of_not_ge hn) hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm,hx] with y hy hy'
    exact le_antisymm hy' hy
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := he.deriv.mono (fun y hy => hy.trans (deriv_const y (f x)))
  have hz : deriv (deriv f) x=0 := hd.deriv_eq.trans (deriv_const x 0)
  exact (ne_of_lt (lt_of_not_ge hn)) hz

/-- At a global minimum the literal geometer-sign weighted Laplacian is nonpositive. -/
theorem laplacian_at_min (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ)
    (hm : ∀ q, u.val (x : CircleHodge.Circle) ≤ u.val q) :
    laplacian ρ u (x : CircleHodge.Circle) ≤ 0 := by
  have hl : IsLocalMin (cover u.val) x := Filter.Eventually.of_forall (fun y => hm (y : CircleHodge.Circle))
  have hd : deriv (cover u.val) x=0 := hl.deriv_eq_zero
  have hdd := second_derivative_nonneg hl ((cover_continuous u.val).continuousAt)
  have hr : 0 < cover ρ.val.val x := ρ.val.property (x : CircleHodge.Circle)
  have hf : deriv (cover (flux ρ u)) x=deriv (deriv (cover u.val)) x / cover ρ.val.val x := by
    change deriv (deriv (cover u.val) / cover ρ.val.val) x=_
    rw [deriv_div ((contDiff_one_iff_deriv.mp (c2_deriv_c1 u)).1 x)
      ((contDiff_one_iff_deriv.mp ρ.property).1 x) hr.ne',hd]
    field_simp [hr.ne']
    ring
  change -(deriv (cover (flux ρ u)) x) / cover ρ.val.val x ≤ 0
  rw [hf]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hdd hr.le)) hr.le

/-- The actual unrestricted positive shift, with no equation or inverse assumed. -/
noncomputable def positive (ρ : RegularDensity) (κ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u+κ•u.val
theorem positive_eq_fullShifted (ρ : RegularDensity) (κ : ℝ) (u : C2Coefficient) :
    positive ρ κ u=fullShifted ρ (-κ) u := by
  simp only [positive,fullShifted,neg_smul,sub_neg_eq_add]
theorem positive_sub (ρ : RegularDensity) (κ : ℝ) (u v : C2Coefficient) :
    positive ρ κ (u-v)=positive ρ κ u-positive ρ κ v := by
  simp only [positive_eq_fullShifted,fullShifted_sub]
theorem positive_constant (ρ : RegularDensity) (κ c : ℝ) :
    positive ρ κ (constantC2 c)=constant (κ*c) := by
  rw [positive,laplacian_of_constant ρ (constantC2 c) c rfl,zero_add]
  rfl
theorem positive_zero (ρ : RegularDensity) (κ : ℝ) : positive ρ κ 0=0 :=
  (positive_constant ρ κ 0).trans (congrArg constant (mul_zero κ))

/-- Weak minimum principle on the actual compact weighted circle. -/
theorem minimum_principle (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u : C2Coefficient)
    (hf : ∀ q, 0≤positive ρ κ u q) : ∀ q, 0≤u.val q := by
  obtain ⟨q,_,hq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty u.val.continuous.continuousOn
  obtain ⟨x,rfl⟩ := Quotient.exists_rep q
  have hm : ∀ y, u.val (x : CircleHodge.Circle) ≤ u.val y := fun y => hq (Set.mem_univ y)
  have hl := laplacian_at_min ρ u x hm
  have hp := hf (x : CircleHodge.Circle)
  change 0≤laplacian ρ u (x : CircleHodge.Circle)+κ*u.val (x : CircleHodge.Circle) at hp
  have hn : 0≤u.val (x : CircleHodge.Circle) := by nlinarith
  exact fun y => hn.trans (hm y)

/-- Pointwise comparison for all actual C2 competitors, not just normalized functions. -/
theorem comparison (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u v : C2Coefficient)
    (h : ∀ q, positive ρ κ u q≤positive ρ κ v q) : ∀ q, u.val q≤v.val q := by
  have hp : ∀ q, 0≤positive ρ κ (v-u) q := by
    rw [positive_sub]
    exact fun q => sub_nonneg.mpr (h q)
  exact fun q => sub_nonneg.mp (minimum_principle ρ κ hκ (v-u) hp q)
theorem positive_injective (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    Injective (positive ρ κ) := fun u v h => Subtype.ext (ContinuousMap.ext (fun q =>
  le_antisymm (comparison ρ κ hκ u v (fun q => (congrArg (fun f : Coefficient => f q) h).le) q)
    (comparison ρ κ hκ v u (fun q => (congrArg (fun f : Coefficient => f q) h).symm.le) q)))

/-- Sharp density-independent supremum estimate, obtained by comparison with constants. -/
theorem supremum_bound (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u : C2Coefficient) :
    ‖u.val‖ ≤ κ⁻¹*‖positive ρ κ u‖ := by
  let M : ℝ := ‖positive ρ κ u‖/κ
  have hM : 0≤M := div_nonneg (norm_nonneg _) hκ.le
  have he : κ*M=‖positive ρ κ u‖ := by dsimp [M];rw [mul_comm,div_mul_cancel₀ _ hκ.ne']
  have hu : ∀ q, u.val q≤M := comparison ρ κ hκ u (constantC2 M) (fun q => by
    rw [positive_constant]
    change positive ρ κ u q≤κ*M
    rw [he]
    exact le_trans (le_abs_self _) ((positive ρ κ u).norm_coe_le_norm q))
  have hl : ∀ q, -M≤u.val q := comparison ρ κ hκ (constantC2 (-M)) u (fun q => by
    rw [positive_constant]
    change κ*(-M)≤positive ρ κ u q
    rw [mul_neg,he]
    exact neg_le_of_abs_le ((positive ρ κ u).norm_coe_le_norm q))
  have hn : ‖u.val‖≤M := (ContinuousMap.norm_le _ hM).mpr (fun q => abs_le.mpr ⟨hl q,hu q⟩)
  simpa only [M,div_eq_mul_inv,mul_comm] using hn

/-- Negative shifts have no actual normalized homogeneous mode. -/
theorem negative_nonresonant (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : ¬Resonant ρ (-κ) := by
  rintro ⟨u,hn,hu⟩
  have he : positive ρ κ u.val=positive ρ κ 0 :=
    (positive_eq_fullShifted ρ κ u.val).trans (hu.trans (positive_zero ρ κ).symm)
  exact hn (congrArg Subtype.val (positive_injective ρ κ hκ he))

/-- Actual existence for every continuous forcing, restoring the constant sector explicitly. -/
theorem exists_solution (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ∃ u : C2Coefficient, positive ρ κ u=f := by
  let g : Compatible ρ := ⟨projectForcing ρ f,project_mean_zero ρ f⟩
  obtain ⟨u,hu,_⟩ := unique_solvability ρ (-κ) (negative_nonresonant ρ κ hκ) g
  let a : ℝ := (weightedMean ρ f/mean ρ.val.val)/κ
  refine ⟨u.val+constantC2 a,?_⟩
  have he : positive ρ κ u.val=projectForcing ρ f := (positive_eq_fullShifted ρ κ u.val).trans hu
  have ha : κ*a=weightedMean ρ f/mean ρ.val.val := by dsimp [a];rw [mul_comm,div_mul_cancel₀ _ hκ.ne']
  rw [positive,laplacian_add,laplacian_of_constant ρ (constantC2 a) a rfl]
  ext q
  have hq := congrArg (fun z : Coefficient => z q) he
  change laplacian ρ u.val q+κ*u.val.val q=f q-weightedMean ρ f/mean ρ.val.val at hq
  change laplacian ρ u.val q+0+κ*(u.val.val q+a)=f q
  nlinarith

/-- An actual C2 solution chosen only after existence has been proved. -/
noncomputable def solve (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : C2Coefficient :=
  Classical.choose (exists_solution ρ κ hκ f)
theorem solve_equation (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    positive ρ κ (solve ρ κ hκ f)=f := Classical.choose_spec (exists_solution ρ κ hκ f)
theorem unique_solve (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ∃! u : C2Coefficient,positive ρ κ u=f :=
  ⟨solve ρ κ hκ f,solve_equation ρ κ hκ f,fun _ hu => positive_injective ρ κ hκ (hu.trans (solve_equation ρ κ hκ f).symm)⟩

theorem positive_add (ρ : RegularDensity) (κ : ℝ) (u v : C2Coefficient) :
    positive ρ κ (u+v)=positive ρ κ u+positive ρ κ v :=
  (congrArg₂ (·+·) (laplacian_add ρ u v) (smul_add κ u.val v.val)).trans (add_add_add_comm _ _ _ _)
theorem positive_smul (ρ : RegularDensity) (κ c : ℝ) (u : C2Coefficient) :
    positive ρ κ (c•u)=c•positive ρ κ u :=
  (congrArg₂ (·+·) (laplacian_smul ρ c u) (smul_comm κ c u.val)).trans (smul_add c _ _).symm
noncomputable def solveLinear (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    Coefficient →ₗ[ℝ] C2Coefficient where
  toFun := solve ρ κ hκ
  map_add' f g := positive_injective ρ κ hκ (by
    rw [solve_equation,positive_add,solve_equation,solve_equation])
  map_smul' c f := positive_injective ρ κ hκ (by
    rw [solve_equation,positive_smul,solve_equation]
    rfl)

/-- The full continuous-forcing solution operator; continuity is proved using comparison. -/
noncomputable def resolvent (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    Coefficient →L[ℝ] Coefficient :=
  (C2Space.subtype.comp (solveLinear ρ κ hκ)).mkContinuous (κ⁻¹)
    (fun f => by
      change ‖(solve ρ κ hκ f).val‖≤κ⁻¹*‖f‖
      simpa only [solve_equation] using supremum_bound ρ κ hκ (solve ρ κ hκ f))
theorem resolvent_apply (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    resolvent ρ κ hκ f=(solve ρ κ hκ f).val := rfl
theorem resolvent_regular (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ContDiff ℝ 2 (cover (resolvent ρ κ hκ f)) := (solve ρ κ hκ f).property
theorem resolvent_equation (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ∃ u : C2Coefficient,u.val=resolvent ρ κ hκ f ∧ positive ρ κ u=f :=
  ⟨solve ρ κ hκ f,rfl,solve_equation ρ κ hκ f⟩
theorem resolvent_nonneg (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient)
    (hf : ∀ q,0≤f q) : ∀ q,0≤resolvent ρ κ hκ f q :=
  minimum_principle ρ κ hκ (solve ρ κ hκ f) (fun q => by rw [solve_equation];exact hf q)
theorem resolvent_monotone (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f g : Coefficient)
    (h : ∀ q,f q≤g q) : ∀ q,resolvent ρ κ hκ f q≤resolvent ρ κ hκ g q :=
  comparison ρ κ hκ (solve ρ κ hκ f) (solve ρ κ hκ g) (fun q => by rw [solve_equation,solve_equation];exact h q)
theorem resolvent_bound (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ‖resolvent ρ κ hκ f‖≤κ⁻¹*‖f‖ := by
  rw [resolvent_apply]
  simpa only [solve_equation] using supremum_bound ρ κ hκ (solve ρ κ hκ f)
theorem resolvent_stability (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f g : Coefficient) :
    ‖resolvent ρ κ hκ f-resolvent ρ κ hκ g‖≤κ⁻¹*‖f-g‖ := by
  simpa only [map_sub] using resolvent_bound ρ κ hκ (f-g)
theorem resolvent_constant (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (c : ℝ) :
    resolvent ρ κ hκ (constant c)=constant (c/κ) := by
  change (solve ρ κ hκ (constant c)).val=(constantC2 (c/κ)).val
  apply congrArg Subtype.val
  apply positive_injective ρ κ hκ
  rw [solve_equation,positive_constant,mul_comm,div_mul_cancel₀ _ hκ.ne']
theorem constant_norm (c : ℝ) : ‖constant c‖=‖c‖ :=
  le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg c)).mpr (fun _ => le_rfl))
    ((constant c).norm_coe_le_norm (0 : CircleHodge.Circle))
/-- Unit constant forcing attains the proposed operator bound. -/
theorem resolvent_bound_attained (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    ‖resolvent ρ κ hκ (constant 1)‖=κ⁻¹ ∧ ‖constant 1‖=1 :=
  ⟨(congrArg norm (resolvent_constant ρ κ hκ 1)).trans ((constant_norm (1/κ)).trans
    ((congrArg abs (one_div κ)).trans (abs_of_pos (inv_pos.mpr hκ)))),(constant_norm 1).trans norm_one⟩

/-- The mean identity is a consequence of the literal solved differential equation. -/
theorem resolvent_weightedMean (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    weightedMean ρ (resolvent ρ κ hκ f)=weightedMean ρ f/κ := by
  rw [resolvent_apply]
  have he := congrArg (meanFunctional ρ) (solve_equation ρ κ hκ f)
  change weightedMean ρ (positive ρ κ (solve ρ κ hκ f))=weightedMean ρ f at he
  rw [positive,weightedMean_add,weightedMean_laplacian,weightedMean_smul,zero_add] at he
  apply (eq_div_iff hκ.ne').mpr
  simpa only [mul_comm] using he

/-- Every actual based computational loop retains its genuine weighted period, scaled by 1/lambda. -/
theorem resolvent_raw_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient)
    (p : Trace 0 0) :
    lineIntegral (ρ.val.val*resolvent ρ κ hκ f) (fromTrace p)=
      κ⁻¹*lineIntegral (ρ.val.val*f) (fromTrace p) := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean]
  change weightedMean ρ (resolvent ρ κ hκ f)*_=κ⁻¹*(weightedMean ρ f*_)
  rw [resolvent_weightedMean,div_eq_mul_inv]
  ring
theorem resolvent_cochain_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient)
    (p : Trace 0 0) :
    period p (meanHarmonic (ρ.val.val*resolvent ρ κ hκ f)).val=
      κ⁻¹*period p (meanHarmonic (ρ.val.val*f)).val := by
  simpa only [lineIntegral_fromTrace_harmonic] using resolvent_raw_period ρ κ hκ f p
theorem unit_forcing_period_positive (ρ : RegularDensity) :
    0<lineIntegral (ρ.val.val*constant 1) (fromTrace unitTrace) := by
  simpa only [lineIntegral_unit,show constant 1=(1 : Coefficient) from rfl,mul_one] using mean_pos ρ.val
theorem unit_solution_period_positive (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    0<lineIntegral (ρ.val.val*resolvent ρ κ hκ (constant 1)) (fromTrace unitTrace) := by
  rw [resolvent_raw_period]
  exact mul_pos (inv_pos.mpr hκ) (unit_forcing_period_positive ρ)
end ComputationalHodge.PositiveResolvent
