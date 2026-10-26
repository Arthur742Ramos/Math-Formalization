module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.CompactGreen.Semantics
open ComputationalHodge.CompactGreen ComputationalHodge.CircleHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator
open ComputationalHodge.MetricHodge ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology MeasureTheory Set Filter
open scoped Topology Uniformity UniformConvergence NNReal ContDiff unitInterval
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
    f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := compatible_iff_periods ρ f

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


-- END material-imported-definition audit
end ComputationalHodge.CompactGreen.Semantics
