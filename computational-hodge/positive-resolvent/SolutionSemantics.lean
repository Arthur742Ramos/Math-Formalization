module
public import Solution
namespace ComputationalHodge.PositiveResolvent.Semantics
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology MeasureTheory Set Filter Function Topology Module
open scoped Topology Uniformity UniformConvergence NNReal ContDiff unitInterval
open ComputationalHodge.PositiveResolvent ComputationalHodge.FullCircleRange
-- BEGIN material-imported-definition audit
example (ρ : RegularDensity) : Domain ρ={u : C2Coefficient // weightedMean ρ u.val=0} := rfl
example (ρ : RegularDensity) (u : Domain ρ) : laplaceData ρ u=⟨laplacian ρ u.val,weightedMean_laplacian ρ u.val⟩ := rfl
example (ρ : RegularDensity) (f : Compatible ρ) : liftData ρ f=⟨solution ρ f,solution_mean_zero ρ f⟩ := rfl
example (ρ : RegularDensity) (μ : ℝ) : reduced ρ μ=(1 : Compatible ρ →L[ℝ] Compatible ρ)-μ•greenMap ρ := rfl
example (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : shifted ρ μ u=laplacian ρ u.val-μ•u.val.val := rfl
example (ρ : RegularDensity) (μ : ℝ) : Resonant ρ μ ↔
    ∃ u : Coefficient,∃ hu : ContDiff ℝ 2 (cover u),
      weightedMean ρ u=0 ∧ u≠0 ∧ laplacian ρ ⟨u,hu⟩-μ•u=0 := by
  constructor
  · rintro ⟨⟨⟨u,hu⟩,hm⟩,hn,he⟩;exact ⟨u,hu,hm,hn,he⟩
  · rintro ⟨u,hu,hm,hn,he⟩;exact ⟨⟨⟨u,hu⟩,hm⟩,hn,he⟩
example (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    (fun f => reducedEquiv ρ μ h f)=(fun f => reduced ρ μ f) := rfl
example (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    Continuous (reducedEquiv ρ μ h).symm := (reducedEquiv ρ μ h).symm.continuous
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
example (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    Function.Bijective (reduced ρ μ) := reduced_bijective ρ μ h
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


example (ρ : RegularDensity) (f : Coefficient) :
    f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := by
  simpa only [lineIntegral_fromTrace_harmonic] using compatible_iff_raw ρ f


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




example (f : ℝ→ℝ) (x : ℝ) : ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) := Iff.rfl
example (x : ℝ) : 𝓝 x=⨅ s∈{s : Set ℝ | x∈s ∧ IsOpen s},Filter.principal s := nhds_def x
example (x : ℝ) (s : Set ℝ) : 𝓝[s] x=𝓝 x ⊓ Filter.principal s := rfl
example (s t : Set ℝ) : t∈Filter.principal s ↔ s⊆t := Iff.rfl
example (f : ℝ→ℝ) (x : ℝ) : IsLocalMin f x ↔ ∀ᶠ y in 𝓝 x,f x≤f y := Iff.rfl
example (f : ℝ→ℝ) (x : ℝ) : IsLocalMax f x ↔ ∀ᶠ y in 𝓝 x,f y≤f x := Iff.rfl
example (f g : ℝ→ℝ) (x : ℝ) : (f =ᶠ[𝓝 x] g) ↔ {y | f y=g y}∈𝓝 x := Iff.rfl
example (f : ℝ→ℝ) (S : Set ℝ) (a : ℝ) : IsMinOn f S a ↔ ∀ y∈S,f a≤f y :=
  ⟨fun h _ hy => h hy,fun h _ hy => h _ hy⟩
example (f : ℝ→ℝ) (x : ℝ) (h : IsLocalMin f x) : deriv f x=0 := h.deriv_eq_zero
example (f g : ℝ→ℝ) (x : ℝ) (h : f =ᶠ[𝓝 x] g) : deriv f x=deriv g x := h.deriv_eq
example (f g : ℝ→ℝ) (x : ℝ) (h : f =ᶠ[𝓝 x] g) : deriv f =ᶠ[𝓝 x] deriv g := h.deriv
example (f : ℝ→ℝ) (x : ℝ) (hs : deriv (deriv f) x<0) (hd : deriv f x=0)
    (hc : ContinuousAt f x) : IsLocalMax f x := isLocalMax_of_deriv_deriv_neg hs hd hc
example (f : ℝ→ℝ) (x : ℝ) (hm : IsLocalMin f x) (hc : ContinuousAt f x) :
    0≤deriv (deriv f) x := second_derivative_nonneg hm hc
example (u : Coefficient) : ∃ q : CircleHodge.Circle,∀ y,u q≤u y := by
  obtain ⟨q,_,hq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty u.continuous.continuousOn
  exact ⟨q,fun y => hq (Set.mem_univ y)⟩
example (f : Coefficient) (C : ℝ) (hC : 0≤C) : ‖f‖≤C ↔ ∀ q,‖f q‖≤C :=
  ContinuousMap.norm_le f hC
example (f : Coefficient) (q : CircleHodge.Circle) : ‖f q‖≤‖f‖ := f.norm_coe_le_norm q
example (L : Coefficient →ₗ[ℝ] Coefficient) (C : ℝ) (h : ∀ f,‖L f‖≤C*‖f‖) :
    (L.mkContinuous C h : Coefficient→Coefficient)=L := rfl
example (L : Coefficient →ₗ[ℝ] Coefficient) (C : ℝ) (h : ∀ f,‖L f‖≤C*‖f‖) :
    Continuous L := AddMonoidHomClass.continuous_of_bound L C h
example (ρ : RegularDensity) (κ : ℝ) (u : C2Coefficient) (x : ℝ) :
    positive ρ κ u (x : CircleHodge.Circle)=
      -(deriv (fun t => deriv (cover u.val) t / cover ρ.val.val t) x)/cover ρ.val.val x+κ*cover u.val x := rfl
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u v : C2Coefficient)
    (h : ∀ q,positive ρ κ u q≤positive ρ κ v q) : ∀ q,u.val q≤v.val q := comparison ρ κ hκ u v h
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u : C2Coefficient) :
    ‖u.val‖≤κ⁻¹*‖positive ρ κ u‖ := supremum_bound ρ κ hκ u
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : ¬Resonant ρ (-κ) := negative_nonresonant ρ κ hκ
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ∃! u : C2Coefficient,positive ρ κ u=f := unique_solve ρ κ hκ f
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    resolvent ρ κ hκ f=(solve ρ κ hκ f).val := rfl
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ContDiff ℝ 2 (cover (resolvent ρ κ hκ f)) := resolvent_regular ρ κ hκ f
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    ∃ u : C2Coefficient,u.val=resolvent ρ κ hκ f ∧ positive ρ κ u=f := resolvent_equation ρ κ hκ f
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (hf : ∀ q,0≤f q) :
    ∀ q,0≤resolvent ρ κ hκ f q := resolvent_nonneg ρ κ hκ f hf
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f g : Coefficient) (h : ∀ q,f q≤g q) :
    ∀ q,resolvent ρ κ hκ f q≤resolvent ρ κ hκ g q := resolvent_monotone ρ κ hκ f g h
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f g : Coefficient) :
    ‖resolvent ρ κ hκ f-resolvent ρ κ hκ g‖≤κ⁻¹*‖f-g‖ := resolvent_stability ρ κ hκ f g
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (c : ℝ) :
    resolvent ρ κ hκ (constant c)=constant (c/κ) := resolvent_constant ρ κ hκ c
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    ‖resolvent ρ κ hκ (constant 1)‖=κ⁻¹ ∧ ‖constant 1‖=1 := resolvent_bound_attained ρ κ hκ
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    weightedMean ρ (resolvent ρ κ hκ f)=weightedMean ρ f/κ := resolvent_weightedMean ρ κ hκ f
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (p : Trace 0 0) :
    lineIntegral (ρ.val.val*resolvent ρ κ hκ f) (fromTrace p)=κ⁻¹*lineIntegral (ρ.val.val*f) (fromTrace p) :=
  resolvent_raw_period ρ κ hκ f p
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (p : Trace 0 0) :
    period p (meanHarmonic (ρ.val.val*resolvent ρ κ hκ f)).val=κ⁻¹*period p (meanHarmonic (ρ.val.val*f)).val :=
  resolvent_cochain_period ρ κ hκ f p
example (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    0<lineIntegral (ρ.val.val*resolvent ρ κ hκ (constant 1)) (fromTrace unitTrace) := unit_solution_period_positive ρ κ hκ
example (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  zero_solvable_iff_raw ρ f

-- END material-imported-definition audit
end ComputationalHodge.PositiveResolvent.Semantics
