module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.FullCircleRange.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.CompactGreen ComputationalHodge.ResonanceObstruction ComputationalHodge.ResonantRange
open MeasureTheory Set Filter Function Topology Module
open scoped Topology Uniformity UniformConvergence NNReal ContDiff unitInterval
example (ρ : RegularDensity) : Domain ρ={u : C2Coefficient // weightedMean ρ u.val=0} := rfl

example (ρ : RegularDensity) (f : Compatible ρ) : liftData ρ f=⟨solution ρ f,solution_mean_zero ρ f⟩ := rfl

example (ρ : RegularDensity) (μ : ℝ) : reduced ρ μ=(1 : Compatible ρ →L[ℝ] Compatible ρ)-μ•greenMap ρ := rfl

example (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : shifted ρ μ u=laplacian ρ u.val-μ•u.val.val := rfl

example (ρ : RegularDensity) (μ : ℝ) : Function.Bijective (reduced ρ μ) ↔
    (∀ x y,reduced ρ μ x=reduced ρ μ y → x=y) ∧ (∀ y,∃ x,reduced ρ μ x=y) := Iff.rfl

example (ρ : RegularDensity) (T : Compatible ρ →L[ℝ] Compatible ρ) (μ : ℝ) (x : Compatible ρ) :
    Module.End.HasEigenvector T.toLinearMap μ x ↔ T x=μ•x ∧ x≠0 := by
  simp only [Module.End.hasEigenvector_iff,Module.End.mem_genEigenspace_one]
  rfl

example (ρ : RegularDensity) (T : Compatible ρ →L[ℝ] Compatible ρ) (μ : ℝ) :
    Module.End.HasEigenvalue T.toLinearMap μ ↔ (Module.End.eigenspace T.toLinearMap μ)≠⊥ := Iff.rfl
-- Literal algebraic definition; actual-H inverse transfer is separately proved below.

example {A : Type*} [Ring A] [Algebra ℝ A] (T : A) (μ : ℝ) :
    μ∈resolventSet ℝ T ↔ IsUnit (algebraMap ℝ A μ-T) := Iff.rfl

example (ρ : RegularDensity) (T : Compatible ρ →L[ℝ] Compatible ρ) :
    IsUnit T ↔ ∃ u : (Compatible ρ →L[ℝ] Compatible ρ)ˣ,(u : Compatible ρ →L[ℝ] Compatible ρ)=T := Iff.rfl
-- Proved contracts on the actual H, not claims of literal unfolding.

example (ρ : RegularDensity) (B : ℝ) : forcingBall ρ B={f : Compatible ρ | ‖f‖≤B} := rfl


example (ρ : RegularDensity) (B : ℝ) : coefficientImage ρ B=(fun f : Compatible ρ => (greenMap ρ f).val) '' forcingBall ρ B := rfl


example (ρ : RegularDensity) (B : ℝ) : valueBound ρ B=4*(mean ρ.val.val)^2*max 0 B := rfl


example (ρ : RegularDensity) (B : ℝ) : (slopeBound ρ B : ℝ)=2*mean ρ.val.val*‖ρ.val.val‖*max 0 B := rfl


example (ρ : RegularDensity) : IsCompactOperator (greenMap ρ) ↔
    ∃ K : Set (Compatible ρ),IsCompact K ∧ (greenMap ρ) ⁻¹' K∈𝓝 (0 : Compatible ρ) := Iff.rfl


example (ρ : RegularDensity) (S : Set (Compatible ρ)) : Bornology.IsBounded S ↔ ∃ C : ℝ,∀ f∈S,‖f‖≤C := isBounded_iff_forall_norm_le


example (Idx : Type*) (F : Idx → CircleHodge.Circle → ℝ) : Equicontinuous F ↔
    ∀ x,∀ U∈𝓤 ℝ,∀ᶠ y in 𝓝 x,∀ i,(F i x,F i y)∈U := Iff.rfl


example (Idx : Type*) (F : Idx → CircleHodge.Circle → ℝ) : Equicontinuous F ↔
    Continuous (UniformFun.ofFun ∘ Function.swap F : CircleHodge.Circle → UniformFun Idx ℝ) := equicontinuous_iff_continuous


example (Idx : Type*) : UniformFun Idx ℝ=(Idx → ℝ) := rfl


example (Idx : Type*) (f : Idx → ℝ) : UniformFun.ofFun f=f := rfl


example (f : ℕ → Coefficient) (l : Filter Coefficient) : Tendsto f atTop l ↔ Filter.map f atTop≤l := Iff.rfl


example (φ : ℕ → ℕ) : StrictMono φ ↔ ∀ a b,a<b → φ a<φ b := Iff.rfl


example : (atTop : Filter ℕ)=⨅ a,Filter.principal (Ici a) := rfl


example (ρ : RegularDensity) : FirstCountableTopology (Compatible ρ) := inferInstance


example (ρ : RegularDensity) (B : ℝ) : IsCompact (closure (coefficientImage ρ B)) := coefficientImage_precompact ρ B


example (ρ : RegularDensity) : IsCompactOperator (greenMap ρ) := green_isCompactOperator ρ


example (S : Set Coefficient) : closure S=⋂₀ {t : Set Coefficient | IsClosed t ∧ S⊆t} := rfl


example : Topology.IsQuotientMap (fun x : ℝ => (x : CircleHodge.Circle)) := isQuotientMap_quotient_mk'


example (ρ : RegularDensity) : Topology.IsClosedEmbedding (Subtype.val : Compatible ρ → Coefficient) := (compatible_closed ρ).isClosedEmbedding_subtypeVal


example (ρ : RegularDensity) : FirstCountableTopology (Compatible ρ) ↔ ∀ u : Compatible ρ,(𝓝 u).IsCountablyGenerated :=
  ⟨fun h => @FirstCountableTopology.nhds_generated_countable _ _ h,fun h => ⟨h⟩⟩


example (Idx : Type*) (U : Set (ℝ×ℝ)) (f g : UniformFun Idx ℝ) :
    (f,g)∈UniformFun.gen Idx ℝ U ↔ ∀ i,(f i,g i)∈U := Iff.rfl


example (Idx : Type*) : (𝓤 (UniformFun Idx ℝ)).HasBasis
    (fun U : Set (ℝ×ℝ) => U∈𝓤 ℝ) (UniformFun.gen Idx ℝ) := UniformFun.hasBasis_uniformity _ _


example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl



example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl



example : RegularDensity={ρ : Density // ContDiff ℝ 1 (cover ρ.val)} := rfl



example : (C2Space : Set Coefficient)={u | ContDiff ℝ 2 (cover u)} := rfl



example (ρ : RegularDensity) (f : Coefficient) : f∈compatibleSpace ρ ↔ weightedMean ρ f=0 := Iff.rfl



example (ρ : RegularDensity) (f : Coefficient) : meanFunctional ρ f=weightedMean ρ f := rfl



example (ρ : RegularDensity) (f : Compatible ρ) : ‖f‖=‖f.val‖ := rfl



example (ρ : RegularDensity) : CompleteSpace (Compatible ρ) := compatible_complete ρ



example : CompactlyCoherentSpace CircleHodge.Circle := inferInstance



example (ρ : RegularDensity) : CompleteSpace (Compatible ρ) ↔ ∀ l : Filter (Compatible ρ),Cauchy l→∃ u,l≤nhds u :=
  ⟨fun h l hl => @CompleteSpace.complete _ _ h l hl,fun h => ⟨fun {l} hl => h l hl⟩⟩



example (ρ : RegularDensity) (l : Filter (Compatible ρ)) (h : Cauchy l) : ∃ u,l≤nhds u := CompleteSpace.complete h



example (ρ : RegularDensity) (l : Filter (Compatible ρ)) : Cauchy l ↔ NeBot l ∧ l×ˢl≤𝓤 (Compatible ρ) := Iff.rfl



example (ρ : RegularDensity) : IsClosed (compatibleSpace ρ : Set Coefficient) := compatible_closed ρ



example (s : Set Coefficient) : IsClosed s ↔ IsOpen sᶜ := ⟨fun h => h.isOpen_compl,fun h => ⟨h⟩⟩



example (f : Coefficient) (C : ℝ) (hC : 0≤C) : ‖f‖≤C ↔ ∀ q,‖f q‖≤C := ContinuousMap.norm_le f hC



example (f : Coefficient) : ‖f‖=sInf {C : ℝ | 0≤C ∧ ∀ q,‖f q‖≤C} :=
  (BoundedContinuousFunction.norm_mkOfCompact f).symm.trans (BoundedContinuousFunction.norm_eq (BoundedContinuousFunction.mkOfCompact f))



example (ρ : RegularDensity) (c : ℝ) (f : Compatible ρ) : ‖c•f‖≤‖c‖*‖f‖ := by
  change ‖c•f.val‖≤‖c‖*‖f.val‖
  exact norm_smul_le c f.val



example (ρ : RegularDensity) (f : Compatible ρ) : ‖f‖=0 ↔ f=0 := norm_eq_zero



example (ρ : RegularDensity) : Continuous (greenMap ρ) := (greenMap ρ).continuous



example (ρ : RegularDensity) (f g : Compatible ρ) : greenMap ρ (f+g)=greenMap ρ f+greenMap ρ g := map_add _ _ _



example (ρ : RegularDensity) (c : ℝ) (f : Compatible ρ) : greenMap ρ (c•f)=c•greenMap ρ f := map_smul _ _ _



example (ρ : RegularDensity) (f : Compatible ρ) : ‖greenMap ρ f‖≤4*(mean ρ.val.val)^2*‖f‖ := greenMap_bound ρ f



example (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ f=∫ q : CircleHodge.Circle,ρ.val.val q*f q := mean_circle _



example (ρ : RegularDensity) (f : Coefficient) :
    f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := compatible_iff_raw ρ f



example (f : ℝ→ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv



example (f : ℝ→ℝ) : ContDiff ℝ 2 f ↔ Differentiable ℝ f ∧ ContDiff ℝ 1 (deriv f) := by
  rw [show (2 : ℕ∞ω)=(1 : ℕ∞ω)+1 from rfl,contDiff_succ_iff_deriv];simp



example {f : ℝ→ℝ} {x v : ℝ} : HasDerivAt f v x ↔ HasDerivAtFilter f v (nhds x×ˢpure x) := Iff.rfl



example {f : ℝ→ℝ} {a b : ℝ} : IntervalIntegrable f volume a b ↔ IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl



example (α : Coefficient) (L : ACLift) : lineIntegral α L=∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl



example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p



example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl




example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl




example : RegularDensity={ρ : Density // ContDiff ℝ 1 (cover ρ.val)} := rfl




example : (C2Space : Set Coefficient)={u | ContDiff ℝ 2 (cover u)} := rfl




example (u : C2Coefficient) : ContDiff ℝ 2 (cover u.val) := u.property




example (f : ℝ→ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv




example (f : ℝ→ℝ) : ContDiff ℝ 2 f ↔ Differentiable ℝ f ∧ ContDiff ℝ 1 (deriv f) := by
  rw [show (2 : ℕ∞ω)=(1 : ℕ∞ω)+1 from rfl,contDiff_succ_iff_deriv]
  simp




example (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) :
    cover (laplacian ρ u) x=-(deriv (fun t => deriv (cover u.val) t/cover ρ.val.val t) x)/cover ρ.val.val x := rfl




example (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ f=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f x := rfl




example (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ f=
    ∫ q : CircleHodge.Circle,ρ.val.val q*f q := mean_circle (ρ.val.val*f)




example (ρ : RegularDensity) (f : Coefficient) (q : CircleHodge.Circle) :
    projectForcing ρ f q=f q-weightedMean ρ f/mean ρ.val.val := rfl




example (ρ : RegularDensity) (u : C2Coefficient) (q : CircleHodge.Circle) :
    (normalize ρ u).val q=u.val q-weightedMean ρ u.val/mean ρ.val.val := rfl




example (ρ : RegularDensity) (f : Coefficient) :
    laplacian ρ (green ρ f)=projectForcing ρ f := green_solves_projected ρ f




example {α : Type} (P : α→Prop) : (∃! x,P x) ↔ ∃ x,P x ∧ ∀ y,P y→y=x := Iff.rfl




example {f : ℝ→ℝ} : Function.Periodic f 1 ↔ ∀ x,f (x+1)=f x := Iff.rfl




example {f : ℝ→ℝ} {x v : ℝ} : HasDerivAt f v x ↔ HasDerivAtFilter f v (nhds x ×ˢ pure x) := Iff.rfl




example {f : ℝ→ℝ} {a b : ℝ} : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl




example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f ↔ IsCompact (closure (Function.support f)) := Iff.rfl




example : Measure.IsOpenPosMeasure (volume : Measure CircleHodge.Circle) := inferInstance




example (P : ℝ→Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff




example (α : Coefficient) (L : ACLift) : lineIntegral α L=
    ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl




example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p




example (coch : Cochain Unit) : coch∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left coch-period c.right coch=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z coch=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩




example (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f x*cover g x := rfl
example (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=
    ∫ q : CircleHodge.Circle,ρ.val.val q*f q*g q := mean_circle _
example (ρ : RegularDensity) : Domain ρ={u : C2Coefficient // weightedMean ρ u.val=0} := rfl
example (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) (x : ℝ) :
    cover (shifted ρ μ u) x=
      -(deriv (fun t => deriv (cover u.val.val) t/cover ρ.val.val t) x)/cover ρ.val.val x-μ*cover u.val.val x := rfl
example (ρ : RegularDensity) (k f : Compatible ρ) :
    modeFunctional ρ k f=mean (ρ.val.val*f.val*k.val) := modeFunctional_apply ρ k f
example (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) :
    f∈orthogonalSpace ρ μ ↔
      ∀ k : Compatible ρ,reduced ρ μ k=0 → pairing ρ f.val k.val=0 := orthogonal_mem ρ μ f
example (ρ : RegularDensity) (μ : ℝ) (x : orthogonalSpace ρ μ) :
    (restrictedOperator ρ μ x).val=μ•greenMap ρ x.val := rfl
example (ρ : RegularDensity) (μ : ℝ) (x : orthogonalSpace ρ μ) :
    (restrictedReduced ρ μ x).val=reduced ρ μ x.val := rfl
example (ρ : RegularDensity) (μ : ℝ) : CompleteSpace (orthogonalSpace ρ μ) := inferInstance
example (ρ : RegularDensity) (μ : ℝ) (F : Filter (orthogonalSpace ρ μ))
    (h : Cauchy F) : ∃ x, F ≤ 𝓝 x := CompleteSpace.complete h
example (ρ : RegularDensity) (μ : ℝ) (F : Filter (orthogonalSpace ρ μ)) :
    Cauchy F ↔ NeBot F ∧ F ×ˢ F ≤ 𝓤 (orthogonalSpace ρ μ) := Iff.rfl
example (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) :
    f ∈ (⨅ k : (reduced ρ μ).ker, (modeFunctional ρ k.val).ker) ↔
      ∀ k : (reduced ρ μ).ker, modeFunctional ρ k.val f=0 := by
  rw [Submodule.mem_iInf]; rfl
example (ρ : RegularDensity) (k f : Compatible ρ) :
    ((ContinuousLinearMap.mul ℝ Coefficient).flip k.val) f.val=f.val*k.val := rfl
example (ρ : RegularDensity) (k f : Compatible ρ) :
    modeFunctional ρ k f=mean (ρ.val.val*(f.val*k.val)) := rfl
example (ρ : RegularDensity) (f : Compatible ρ) :
    (compatibleSpace ρ).subtypeL f=f.val := rfl
example (ρ : RegularDensity) (μ : ℝ) (x : orthogonalSpace ρ μ) :
    (((μ • greenMap ρ).domRestrict (orthogonalSpace ρ μ)) x)=
      (μ • greenMap ρ) x.val := rfl
example (ρ : RegularDensity) (μ : ℝ) (x : orthogonalSpace ρ μ) :
    ((((μ • greenMap ρ).domRestrict (orthogonalSpace ρ μ)).codRestrict
      (orthogonalSpace ρ μ) (fun z => orthogonal_invariant ρ μ z.val z.property)) x).val=
      (μ • greenMap ρ) x.val := rfl
example (ρ : RegularDensity) (μ : ℝ)
    (A B : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ) (x : orthogonalSpace ρ μ) :
    (A*B) x=A (B x) := rfl
example (ρ : RegularDensity) (μ : ℝ) (x : orthogonalSpace ρ μ) :
    (1 : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ) x=x := rfl
example (ρ : RegularDensity) (μ : ℝ)
    (e : Units (orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ))
    (x : orthogonalSpace ρ μ) : e.inv (e.val x)=x :=
  congrArg (fun A : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ => A x) e.inv_val
example (ρ : RegularDensity) (μ : ℝ)
    (e : Units (orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ))
    (x : orthogonalSpace ρ μ) : e.val (e.inv x)=x :=
  congrArg (fun A : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ => A x) e.val_inv
example (c x y : ℝ) : dist (x+c) (y+c)=dist x y := (isometry_add_right c).dist_eq x y
example (c : ℝ) : LipschitzWith 1 (fun x : ℝ => x+c) := (isometry_add_right c).lipschitzWith
example (c : ℝ) : LipschitzWith 1 (fun x : ℝ => min c x) := LipschitzWith.id.const_min c
example (c : ℝ) : LipschitzWith 1 (fun x : ℝ => max c x) := LipschitzWith.id.const_max c
example (f g : Coefficient) : ‖f*g‖ ≤ ‖f‖*‖g‖ := norm_mul_le f g
example (ρ : RegularDensity) (A : Compatible ρ →L[ℝ] ℝ)
    (B : Compatible ρ →L[ℝ] Compatible ρ) (f : Compatible ρ) :
    A.comp B f=A (B f) := rfl
example {f g : ℝ → ℝ} {K L : ℝ≥0} {c : ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hc : f c=g c) :
    LipschitzWith (K+L) (fun x => if x≤c then f x else g x) := cut_lipschitz hf hg hc
example {f g : ℝ → ℝ} {c : ℝ} (hc : f c=g c) :
    (fun x => if x≤c then f x else g x)=(fun x => f (min c x)+g (max c x)-f c) := by
  funext x
  split_ifs with hx
  · simp only [min_eq_right hx,max_eq_left hx,hc,add_sub_cancel_right]
  · simp only [min_eq_left (not_le.mp hx).le,max_eq_right (not_le.mp hx).le,add_sub_cancel_left]
example (ρ : RegularDensity) (f g : Coefficient) :
    Integrable (fun q : CircleHodge.Circle => ρ.val.val q*f q*g q) volume :=
  continuous_integrable (ρ.val.val*f*g).continuous
example (f : CircleHodge.Circle→ℝ) : Function.support f={q | f q≠0} := rfl
example (f : Coefficient) : IsOpen (Function.support f) := f.continuous.isOpen_support
example (ν : Measure CircleHodge.Circle) : ν.IsOpenPosMeasure ↔
    ∀ U : Set CircleHodge.Circle,IsOpen U → U.Nonempty → ν U≠0 :=
  ⟨fun h => h.open_pos,fun h => ⟨h⟩⟩
open ComputationalHodge.FullCircleRange
example (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) (x : ℝ) :
    cover (fullShifted ρ μ u) x=
      -(deriv (fun t => deriv (cover u.val) t/cover ρ.val.val t) x)/cover ρ.val.val x-μ*cover u.val x := rfl
example (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ μ u=f) ↔
      ∀ v : C2Coefficient,fullShifted ρ μ v=0 →
        (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f x*cover v.val x)=0 :=
  solvable_iff_modes ρ μ f
example (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := zero_solvable_iff_raw ρ f
example (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := zero_solvable_iff_cochain ρ f
example (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) (f : Coefficient)
    (u : C2Coefficient) (hu : fullShifted ρ μ u=projectForcing ρ f) :
    fullShifted ρ μ (u-constantC2 ((weightedMean ρ f/mean ρ.val.val)/μ))=f := reconstruct ρ μ hμ f u hu
example (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    fullShifted ρ μ (Poisson.normalize ρ u)=projectForcing ρ (fullShifted ρ μ u) := normalization_commutes ρ μ u
example (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    fullShifted ρ μ (constantC2 (-1/μ))=constant 1 := constant_solution ρ μ hμ
example (ρ : RegularDensity) :
    0<lineIntegral (ρ.val.val*constant 1) (fromTrace unitTrace) := constant_unit_period_positive ρ
example (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    (∃ u : C2Coefficient,fullShifted ρ μ u=constant 1) ∧
      0<lineIntegral (ρ.val.val*constant 1) (fromTrace unitTrace) := off_zero_periods_not_necessary ρ μ hμ
example (ρ : RegularDensity) (μ : ℝ)
    (e : Units (orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ)) :
    Function.Bijective e.val := (ContinuousLinearEquiv.ofUnit e).bijective
example (ρ : RegularDensity) (μ : ℝ)
    (e : Units (orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ)) (x : orthogonalSpace ρ μ) :
    ContinuousLinearEquiv.ofUnit e x=e.val x := rfl

end ComputationalHodge.FullCircleRange.Semantics
-- END material-imported-definition audit
