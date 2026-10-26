module
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Calculus.DerivativeTest
/-! Complete retained proofs and documented exact adaptations. -/
@[expose] public section
/-
Copyright (c) 2025 Computational Paths contributors.
Upstream excerpts are MIT licensed; see SOURCE-LICENSE.txt.
Ported at the exact revision recorded in source-provenance.json.
-/
/-! Minimal literal source port of the user's endpoint-changing trace and scoped rewrite definitions. Only imports, module visibility and enclosing namespaces are adapted. No claim about equality-indexed raw Path or HoTT is made. -/
namespace ComputationalPaths.Path.GeometricTopology
open scoped ContinuousMap Topology
universe u v
structure GeometricStepSystem (A : Type u) [TopologicalSpace A] (Step : Type v) where
  src : Step → A
  tgt : Step → A
  realize : (s : Step) → _root_.Path (src s) (tgt s)
/-- A finite trace of endpoint-changing geometric computations. -/
inductive GeometricTrace {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) : A → A → Type (max u v) where
  | refl (a : A) : GeometricTrace S a a
  | single (s : Step) : GeometricTrace S (S.src s) (S.tgt s)
  | trans {a b c : A} :
      GeometricTrace S a b → GeometricTrace S b c → GeometricTrace S a c
  | symm {a b : A} : GeometricTrace S a b → GeometricTrace S b a
namespace GeometricTrace
variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}
/-- The continuous path obtained by executing a geometric trace. -/
noncomputable def realize {a b : A} : GeometricTrace S a b → _root_.Path a b
  | .refl a => _root_.Path.refl a
  | .single s => S.realize s
  | .trans p q => _root_.Path.trans (realize p) (realize q)
  | .symm p => _root_.Path.symm (realize p)
end GeometricTrace
structure ContinuousGeometricStepSystem (A : Type u) [TopologicalSpace A] (Step : Type v) [TopologicalSpace Step] extends GeometricStepSystem A Step where
  continuous_src : Continuous src
  continuous_tgt : Continuous tgt
  continuous_realize :
    Continuous (fun s => (realize s).toContinuousMap)
structure ScopedGeometricRewritePresentation {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step] (S : ContinuousGeometricStepSystem A Step) where
  rule : ∀ {a b : A},
    GeometricTrace S.toGeometricStepSystem a b →
      GeometricTrace S.toGeometricStepSystem a b → Prop
  sound_rule : ∀ {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b},
    rule p q →
      _root_.Path.Homotopic
        (GeometricTrace.realize p) (GeometricTrace.realize q)
end ComputationalPaths.Path.GeometricTopology
namespace ComputationalHodge
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E]
abbrev Cochain (E : Type v) [Fintype E] := EuclideanSpace ℝ E
def evaluation (e : E) : Cochain E →ₗ[ℝ] ℝ where
  toFun ω := ω e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- The actual signed integral of edge coefficients along a computational trace. -/ def period {S : GeometricStepSystem A E} {a b : A} : GeometricTrace S a b → Cochain E →ₗ[ℝ] ℝ
  | .refl _ => 0
  | .single e => evaluation e
  | .trans p q => period p + period q
  | .symm p => -period p
/-- The degree-zero coboundary, with actual source and target evaluations. -/ def d0 (S : GeometricStepSystem A E) : (A → ℝ) →ₗ[ℝ] Cochain E where
  toFun f := WithLp.toLp 2 (fun e => f (S.tgt e) - f (S.src e))
  map_add' f g := by
    ext e
    change (f (S.tgt e) + g (S.tgt e)) - (f (S.src e) + g (S.src e)) = _
    change _ = (f (S.tgt e) - f (S.src e)) + (g (S.tgt e) - g (S.src e))
    ring
  map_smul' r f := by
    ext e
    change r * f (S.tgt e) - r * f (S.src e) = r * (f (S.tgt e) - f (S.src e))
    ring
variable [TopologicalSpace E] {S : ContinuousGeometricStepSystem A E}
/-- All named rules, including their endpoints: no unlisted-rule assumption. -/ structure Cell (P : ScopedGeometricRewritePresentation S) where
  src : A
  tgt : A
  left : GeometricTrace S.toGeometricStepSystem src tgt
  right : GeometricTrace S.toGeometricStepSystem src tgt
  rule : P.rule left right
/-- The next coboundary evaluates every named relation's actual period difference. -/ def d1 (P : ScopedGeometricRewritePresentation S) : Cochain E →ₗ[ℝ] (Cell P → ℝ) :=
  LinearMap.pi fun c => period c.left - period c.right
def Closed (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Cochain E) :=
  LinearMap.ker (d1 P)
def Exact (S : ContinuousGeometricStepSystem A E) : Submodule ℝ (Cochain E) :=
  LinearMap.range (d0 S.toGeometricStepSystem)
end ComputationalHodge
namespace ComputationalHodge
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}
noncomputable def Harmonic (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Cochain E) :=
  Closed P ⊓ (Exact S)ᗮ
end ComputationalHodge
namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}
/-- Complete geometric relations are actual endpoint-fixed path homotopies. -/ noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) : ScopedGeometricRewritePresentation S where
  rule p q := _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule h := h
end ComputationalHodge.LoopCharacters
namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
open scoped unitInterval
/-- The ordinary covering of the unit additive circle by the real line. -/ theorem circleCover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1
noncomputable def circleLift (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) : C(unitInterval,ℝ) :=
  circleCover.liftPath p.toContinuousMap 0 (by simp)
noncomputable def winding (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) : ℝ := circleLift p 1
theorem winding_homotopic {p q : _root_.Path (0 : AddCircle (1 : ℝ)) 0} (h : _root_.Path.Homotopic p q) : winding p = winding q :=
  circleCover.liftPath_apply_one_eq_of_homotopicRel h 0 (by simp) (by simp)
def onceAround : _root_.Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := by simp
  target' := by simp
end ComputationalHodge.LoopCharacters
namespace ComputationalHodge.CircleHodge
open Set
abbrev Circle := AddCircle (1 : ℝ)
abbrev Coefficient := C(Circle,ℝ)
def cover (α : Coefficient) (x : ℝ) : ℝ := α (x : Circle)
theorem cover_continuous (α : Coefficient) : Continuous (cover α) := by
  unfold cover
  fun_prop
theorem cover_periodic (α : Coefficient) : Function.Periodic (cover α) 1 := by
  intro x
  simp [cover,Circle]
def constant (c : ℝ) : Coefficient := ContinuousMap.const Circle c
noncomputable def mean (α : Coefficient) : ℝ := ∫ x in (0 : ℝ)..1,cover α x
end ComputationalHodge.CircleHodge
namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
/-- One actual circle loop as a finite computational generator. -/ def circleSystem : ContinuousGeometricStepSystem (AddCircle (1 : ℝ)) Unit where
  src _ := 0
  tgt _ := 0
  realize _ := onceAround
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_const
end ComputationalHodge.LoopCharacters
namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open scoped NNReal Topology unitInterval
abbrev Trace (a b : CircleHodge.Circle) := GeometricTrace circleSystem.toGeometricStepSystem a b
def count {a b : CircleHodge.Circle} : Trace a b → ℤ
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => count p+count q
  | .symm p => -count p
def clamp (t : ℝ) : ℝ := max 0 (min 1 t)
/-- A finite piecewise-affine construction from the actual trace syntax. Equality with the actual covering lift is proved separately. -/ noncomputable def rawLift {a b : CircleHodge.Circle} : Trace a b → ℝ → ℝ
  | .refl _ => fun _ => 0
  | .single _ => clamp
  | .trans p q => fun t => if t≤1/2 then rawLift p (2*t)
      else rawLift p 1+rawLift q (2*t-1)
  | .symm p => fun t => rawLift p (1-t)-rawLift p 1
theorem trace_endpoints {a b : CircleHodge.Circle} (p : Trace a b) : a=b := by induction p <;> aesop
theorem rawLift_zero {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 0=0 := by induction p <;> simp_all [rawLift,clamp]
theorem rawLift_one {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 1=(count p : ℝ) := by
  induction p <;> simp_all [rawLift,count,clamp,rawLift_zero]; norm_num; assumption
theorem cut_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0} {c : ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hc : f c=g c) : LipschitzWith (K+L) (fun x => if x≤c then f x else g x) := by
  have hh : LipschitzWith (K+L) (fun x => f (min c x)+g (max c x)-f c) := by
    simpa only [Function.comp_def,id_eq,mul_one,one_mul,sub_eq_add_neg] using (isometry_add_right (-f c)).lipschitzWith.comp
      ((hf.comp (LipschitzWith.id.const_min c)).add (hg.comp (LipschitzWith.id.const_max c)))
  convert hh using 1
  funext x
  split_ifs with hx
  · simp only [min_eq_right hx,max_eq_left hx,hc,add_sub_cancel_right]
  · simp only [min_eq_left (not_le.mp hx).le,max_eq_right (not_le.mp hx).le,add_sub_cancel_left]
theorem affine_lipschitz (a b : ℝ) : LipschitzWith ‖a‖₊ (fun x : ℝ => a*x+b) := by simpa only [Function.comp_def,smul_eq_mul,one_mul] using (isometry_add_right b).lipschitzWith.comp (lipschitzWith_smul a)
theorem shift_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) : LipschitzWith K (fun x => c+f x) := by simpa only [Function.comp_def,one_mul] using (isometry_add_left c).lipschitzWith.comp hf
theorem rawLift_lipschitz {a b : CircleHodge.Circle} (p : Trace a b) : ∃ K : ℝ≥0,LipschitzWith K (rawLift p) := by
  induction p with
  | refl _ => exact ⟨0,LipschitzWith.const 0⟩
  | single _ => exact ⟨1,(LipschitzWith.id.const_min 1).const_max 0⟩
  | trans p q hp hq => exact hp.elim (fun K hK => hq.elim (fun L hL => ⟨K*‖(2:ℝ)‖₊+L*‖(2:ℝ)‖₊,
      cut_lipschitz (by simpa only [Function.comp_def,add_zero] using hK.comp (affine_lipschitz 2 0))
        (shift_lipschitz (by simpa only [Function.comp_def,sub_eq_add_neg] using hL.comp (affine_lipschitz 2 (-1))) (rawLift p 1)) (by norm_num [rawLift_zero])⟩))
  | symm p hp => exact hp.elim (fun K hK => ⟨K*‖(-1:ℝ)‖₊,by
      change LipschitzWith (K*‖(-1:ℝ)‖₊) (fun x => rawLift p (1-x)-rawLift p 1)
      simpa only [sub_eq_add_neg,add_comm,Function.comp_def,neg_one_mul] using
        shift_lipschitz (hK.comp (affine_lipschitz (-1) 1)) (-rawLift p 1)⟩)
theorem rawLift_continuous {a b : CircleHodge.Circle} (p : Trace a b) : Continuous (rawLift p) := (rawLift_lipschitz p).choose_spec.continuous
theorem rawLift_one_coe {a b : CircleHodge.Circle} (p : Trace a b) : ((rawLift p 1 : ℝ) : CircleHodge.Circle)=0 := (congrArg (fun x : ℝ => (x : CircleHodge.Circle)) (rawLift_one p)).trans
  ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨count p,by simp⟩)
theorem rawLift_projects {a b : CircleHodge.Circle} (p : Trace a b) (t : unitInterval) : ((rawLift p (t : ℝ) : ℝ) : CircleHodge.Circle)+a=GeometricTrace.realize p t := by
  induction p generalizing t with
  | refl a => simp [rawLift,GeometricTrace.realize]
  | single e =>
    change ((clamp (t : ℝ) : ℝ) : CircleHodge.Circle)+0=((t : ℝ) : CircleHodge.Circle)
    simp [clamp,min_eq_right t.2.2,max_eq_right t.2.1]
  | trans p q hp hq =>
    rw [GeometricTrace.realize,_root_.Path.trans_apply]
    simp only [rawLift]
    split_ifs with h
    · exact hp ⟨2*t,⟨by linarith [t.2.1],by linarith⟩⟩
    · simpa only [AddCircle.coe_add,rawLift_one_coe,zero_add,trace_endpoints p] using hq ⟨2*t-1,⟨by linarith [not_le.mp h],by linarith [t.2.2]⟩⟩
  | symm p hp =>
    simpa only [rawLift,GeometricTrace.realize,_root_.Path.symm_apply,Function.comp_apply,unitInterval.coe_symm_eq,AddCircle.coe_sub,rawLift_one_coe,sub_zero,trace_endpoints p] using hp (σ t)
theorem rawLift_outside {a b : CircleHodge.Circle} (p : Trace a b) : ∀ t : ℝ,(t≤0 → rawLift p t=0) ∧ (1≤t → rawLift p t=rawLift p 1) := by
  induction p <;> intro t <;> constructor <;> intro ht
  all_goals simp only [rawLift,clamp,min_def,max_def] at *
  all_goals grind [rawLift_zero]
theorem rawLift_clamp {a b : CircleHodge.Circle} (p : Trace a b) (t : ℝ) : rawLift p (Set.projIcc 0 1 zero_le_one t : ℝ)=rawLift p t := by
  by_cases h0 : t≤0
  · rw [Set.projIcc_of_le_left zero_le_one h0]
    exact (rawLift_zero p).trans ((rawLift_outside p t).1 h0).symm
  by_cases h1 : 1≤t
  · rw [Set.projIcc_of_right_le zero_le_one h1]
    exact ((rawLift_outside p t).2 h1).symm
  rw [Set.projIcc_of_mem zero_le_one ⟨(not_le.mp h0).le,(not_le.mp h1).le⟩]
/-- The actual covering lift of the actual path, extended by the interval projection. -/ noncomputable def actualLift (p : Trace 0 0) (t : ℝ) : ℝ :=
  circleLift (GeometricTrace.realize p) (Set.projIcc 0 1 zero_le_one t)
theorem rawLift_eq_cover (p : Trace 0 0) (t : unitInterval) : rawLift p (t : ℝ)=circleLift (GeometricTrace.realize p) t := congrArg (fun f : C(unitInterval,ℝ) => f t)
  (show (⟨fun t : unitInterval => rawLift p (t : ℝ),(rawLift_continuous p).comp continuous_subtype_val⟩ : C(unitInterval,ℝ))=circleLift (GeometricTrace.realize p) from
    (circleCover.eq_liftPath_iff' _).mpr ⟨funext (fun u => by simpa using rawLift_projects p u),rawLift_zero p⟩)
theorem actualLift_eq_rawLift (p : Trace 0 0) : actualLift p=rawLift p := funext fun t => (rawLift_eq_cover p (Set.projIcc 0 1 zero_le_one t)).symm.trans (rawLift_clamp p t)
end ComputationalHodge.TraceIntegrals
namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
def unitTrace : Trace 0 0 := .single ()
noncomputable def meanCochain (α : Coefficient) : Cochain Unit := WithLp.toLp 2 (fun _ => mean α)
theorem period_mean_count (α : Coefficient) {a b : CircleHodge.Circle} (p : Trace a b) : period p (meanCochain α)=mean α*(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change mean α=mean α*((1 : ℤ) : ℝ);rw [Int.cast_one,mul_one]
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add];ring
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg];ring
theorem count_zero_of_source_ne {a b : CircleHodge.Circle} (p : Trace a b) : a≠0 → count p=0 := by
  induction p with
  | refl _ => exact fun _ => rfl
  | single _ => exact fun h => (h rfl).elim
  | trans p q hp hq => exact fun h => by rw [count,hp h,hq (fun hb => h ((trace_endpoints p).trans hb)),zero_add]
  | symm p hp => exact fun h => by rw [count,hp (fun ha => h ((trace_endpoints p).symm.trans ha)),neg_zero]
theorem winding_realize_count (p : Trace 0 0) : winding (GeometricTrace.realize p)=(count p : ℝ) := (rawLift_eq_cover p 1).symm.trans (rawLift_one p)
theorem count_homotopic {a b : CircleHodge.Circle} (p q : Trace a b) (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) : count p=count q := by
  by_cases ha : a=0
  · subst a
    have hb := trace_endpoints p
    subst b
    have hw : (count p : ℝ)=(count q : ℝ) :=
      (winding_realize_count p).symm.trans ((winding_homotopic h).trans (winding_realize_count q))
    exact_mod_cast hw
  · rw [count_zero_of_source_ne p ha,count_zero_of_source_ne q ha]
theorem meanCochain_closed (α : Coefficient) : meanCochain α∈Closed (geometricPresentation circleSystem) := by
  change d1 (geometricPresentation circleSystem) (meanCochain α)=0
  funext c
  change period c.left (meanCochain α)-period c.right (meanCochain α)=0
  rw [period_mean_count,period_mean_count,count_homotopic c.left c.right c.rule,sub_self]
theorem circle_exact_eq_bot : Exact circleSystem=⊥ := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    change d0 circleSystem.toGeometricStepSystem f=0
    ext e
    exact sub_self (f 0)
  · exact bot_le
noncomputable def meanHarmonic (α : Coefficient) : Harmonic (geometricPresentation circleSystem) :=
  ⟨meanCochain α,meanCochain_closed α,
    by rw [circle_exact_eq_bot,Submodule.bot_orthogonal_eq_top];trivial⟩
end ComputationalHodge.TraceIntegrals
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- A real lift with regularity only on the interval, not a presumed period formula. -/ abbrev ACLift := {f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
  f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0}
def projectedLoop (L : ACLift) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((L.val (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    exact L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)
  source' := by simpa using congrArg (fun x : ℝ => (x : CircleHodge.Circle)) L.property.2.1
  target' := L.property.2.2
/-- Ordinary integration on this actual projected curve, against its real-lift derivative. -/ noncomputable def lineIntegral (α : Coefficient) (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t
noncomputable def primitive (α : Coefficient) (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u,cover α x
theorem primitive_hasDerivAt (α : Coefficient) (x : ℝ) : HasDerivAt (primitive α) (cover α x) x :=
  intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cover_continuous α).continuousAt
theorem primitive_lipschitz (α : Coefficient) : ∃ K : ℝ≥0,LipschitzWith K (primitive α) := ⟨‖α‖₊,lipschitzWith_of_nnnorm_deriv_le
    (fun x => (primitive_hasDerivAt α x).differentiableAt)
    (fun x => by rw [(primitive_hasDerivAt α x).deriv];exact NNReal.coe_le_coe.mp (α.norm_coe_le_norm (x : CircleHodge.Circle)))⟩
theorem primitive_comp_ac (α : Coefficient) (L : ACLift) : AbsolutelyContinuousOnInterval (fun t => primitive α (L.val t)) 0 1 := (primitive_lipschitz α).choose_spec.comp_absolutelyContinuousOnInterval L.property.1
theorem chain_rule_ae (α : Coefficient) (L : ACLift) : ∀ᵐ t : ℝ, t∈uIcc (0 : ℝ) 1 → deriv (fun x => primitive α (L.val x)) t=cover α (L.val t)*deriv L.val t := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hmem
  exact ((primitive_hasDerivAt α (L.val t)).comp t (ht hmem).hasDerivAt).deriv
theorem cover_integrand_integrable (α : Coefficient) (L : ACLift) : IntervalIntegrable (fun t => cover α (L.val t)*deriv L.val t) volume 0 1 := (primitive_comp_ac α L).intervalIntegrable_deriv.congr_ae
    (((ae_restrict_mem measurableSet_uIoc).and (ae_restrict_of_ae (chain_rule_ae α L))).mono
      (fun _t ht => ht.2 (uIoc_subset_uIcc ht.1)))
theorem lineIntegral_eq_cover (α : Coefficient) (L : ACLift) : lineIntegral α L=∫ t in (0 : ℝ)..1,cover α (L.val t)*deriv L.val t := intervalIntegral.integral_congr (fun t ht =>
    congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t)
      (Set.projIcc_of_mem zero_le_one (by simpa only [uIcc_of_le zero_le_one] using ht)))
theorem line_integrand_integrable (α : Coefficient) (L : ACLift) : IntervalIntegrable (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t) volume 0 1 := (cover_integrand_integrable α L).congr (fun t ht =>
    (congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t)
      (Set.projIcc_of_mem zero_le_one (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))).symm)
theorem lineIntegral_eq_endpoint (α : Coefficient) (L : ACLift) : lineIntegral α L=∫ x in (0 : ℝ)..L.val 1,cover α x := by
  rw [lineIntegral_eq_cover]
  calc
    _ = ∫ t in (0 : ℝ)..1,deriv (fun x => primitive α (L.val x)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [chain_rule_ae α L] with t ht hmem
      exact (ht (uIoc_subset_uIcc hmem)).symm
    _ = _ := by simpa [primitive,L.property.2.1] using (primitive_comp_ac α L).integral_deriv_eq_sub
theorem endpoint_integral (L : ACLift) : ∃ n : ℤ,(n : ℝ)=L.val 1 := by
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp L.property.2.2
  exact ⟨n,by simpa using hn⟩
theorem lineIntegral_eq_mean (α : Coefficient) (L : ACLift) : lineIntegral α L=mean α*L.val 1 := by
  obtain ⟨n,hn⟩ := endpoint_integral L
  rw [lineIntegral_eq_endpoint,← hn]
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq n 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simpa [mean,mul_comm] using h
end ComputationalHodge.ACLifts
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Every actual raw finite computational trace is admitted without smoothing it. -/ noncomputable def fromTrace (p : Trace 0 0) : ACLift := ⟨actualLift p,
    (actualLift_eq_rawLift p).symm ▸ (rawLift_lipschitz p).choose_spec.lipschitzOnWith.absolutelyContinuousOnInterval,
    (congrFun (actualLift_eq_rawLift p) 0).trans (rawLift_zero p),
    (congrArg (fun f : ℝ→ℝ => (f 1 : CircleHodge.Circle)) (actualLift_eq_rawLift p)).trans (rawLift_one_coe p)⟩
theorem projected_fromTrace (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := DFunLike.ext _ _ (fun t => by
    simpa [projectedLoop,fromTrace,actualLift,circleLift,Set.projIcc_of_mem zero_le_one t.property] using
      congrFun (circleCover.liftPath_lifts (GeometricTrace.realize p).toContinuousMap 0 (by simp)) t)
theorem lineIntegral_fromTrace_harmonic (α : Coefficient) (p : Trace 0 0) : lineIntegral α (fromTrace p)=period p (meanHarmonic α) := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift p 1=period p (meanCochain α)
  rw [actualLift_eq_rawLift,rawLift_one,period_mean_count]
theorem lineIntegral_unit (α : Coefficient) : lineIntegral α (fromTrace unitTrace)=mean α := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift unitTrace 1=mean α
  rw [actualLift_eq_rawLift,rawLift_one]
  simp [unitTrace,count]
end ComputationalHodge.ACLifts
namespace ComputationalHodge.CircleHodge
open Set
/-- A genuine real primitive with its mean term removed. -/ noncomputable def realPotential (α : Coefficient) (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x,cover α t)-x*mean α
theorem realPotential_hasDerivAt (α : Coefficient) (x : ℝ) : HasDerivAt (realPotential α) (cover α x-mean α) x := (intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter (cover_continuous α).continuousAt).sub
    (by simpa using (hasDerivAt_id x).mul_const (mean α))
theorem realPotential_contDiff (α : Coefficient) : ContDiff ℝ 1 (realPotential α) := contDiff_one_iff_deriv.mpr ⟨fun x => (realPotential_hasDerivAt α x).differentiableAt,
    ((cover_continuous α).sub continuous_const).congr (fun x => (realPotential_hasDerivAt α x).deriv.symm)⟩
theorem realPotential_periodic (α : Coefficient) : Function.Periodic (realPotential α) 1 := by
  intro x
  have h := (cover_periodic α).intervalIntegral_add_eq_add 0 x
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simp only [zero_add] at h
  change (∫ t in (0 : ℝ)..(x+1),cover α t)-(x+1)*mean α = _
  rw [h]
  change ((∫ t in (0 : ℝ)..x,cover α t)+mean α)-(x+1)*mean α = _
  unfold realPotential
  ring
/-- The primitive descends to an actual continuous function on the circle. -/ noncomputable def potential (α : Coefficient) : Coefficient where
  toFun := (realPotential_periodic α).lift
  continuous_toFun := (realPotential_contDiff α).continuous.quotient_liftOn' _
theorem potential_contDiff (α : Coefficient) : ContDiff ℝ 1 (cover (potential α)) :=
  realPotential_contDiff α
theorem potential_deriv (α : Coefficient) (x : ℝ) : deriv (cover (potential α)) x=cover α x-mean α :=
  (realPotential_hasDerivAt α x).deriv
/-- Exactness requires an actual circle potential and its actual C¹ derivative. -/ def ExactCoefficient (α : Coefficient) : Prop :=
  ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x
theorem mean_sub (α β : Coefficient) : mean (α-β)=mean α-mean β := by
  change (∫ x in (0 : ℝ)..1,cover α x-cover β x)=_
  exact intervalIntegral.integral_sub ((cover_continuous α).intervalIntegrable 0 1)
    ((cover_continuous β).intervalIntegrable 0 1)
theorem exact_mean_zero {α : Coefficient} (h : ExactCoefficient α) : mean α=0 := by
  obtain ⟨F,hF,hd⟩ := h
  exact (intervalIntegral.integral_congr (fun x _ => (hd x).symm)).trans
    ((intervalIntegral.integral_deriv_of_contDiffOn_Icc hF.contDiffOn (by norm_num : (0 : ℝ)≤1)).trans
      (sub_eq_zero.mpr (by simpa only [zero_add] using cover_periodic F 0)))
end ComputationalHodge.CircleHodge
namespace ComputationalHodge.MetricHodge
open ComputationalHodge.CircleHodge MeasureTheory Set
/-- Positive continuous length density. The coordinate convention is ds=ρ dx. -/ abbrev Density := {ρ : Coefficient // ∀ q,0<ρ q}
theorem density_ne (ρ : Density) (q : CircleHodge.Circle) : ρ.val q≠0 :=
  ne_of_gt (ρ.property q)
theorem continuous_integrable {f : CircleHodge.Circle→ℝ} (h : Continuous f) : Integrable f volume := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem mean_circle (α : Coefficient) : mean α=∫ q : CircleHodge.Circle,α q := by
  simpa [mean,cover] using (UnitAddCircle.intervalIntegral_preimage 0 α)
theorem mean_pos (ρ : Density) : 0<mean ρ.val := by
  rw [mean_circle]
  exact integral_pos_of_integrable_nonneg_nonzero ρ.val.continuous
    (continuous_integrable ρ.val.continuous) (fun q => (ρ.property q).le) (density_ne ρ 0)
theorem mean_smul (c : ℝ) (α : Coefficient) : mean (c•α)=c*mean α := by
  simp only [mean_circle,ContinuousMap.smul_apply,smul_eq_mul]
  exact integral_const_mul c _
end ComputationalHodge.MetricHodge
namespace ComputationalHodge.Poisson
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
/-- Positive C¹ length density, in the coordinate convention ds=ρ dx. -/ abbrev RegularDensity := {ρ : Density // ContDiff ℝ 1 (cover ρ.val)}
/-- Actual C² circle functions, not arbitrary real functions with totalized derivatives. -/ def C2Space : Submodule ℝ Coefficient where
  carrier := {u | ContDiff ℝ 2 (cover u)}
  zero_mem' := by change ContDiff ℝ 2 (fun _ : ℝ => 0);exact contDiff_const
  add_mem' := by intro u v hu hv;change ContDiff ℝ 2 (cover u) at hu;change ContDiff ℝ 2 (cover v) at hv;exact hu.add hv
  smul_mem' := by intro c u hu;change ContDiff ℝ 2 (cover u) at hu;exact hu.const_smul c
abbrev C2Coefficient := ↥C2Space
theorem c2_c1 (u : C2Coefficient) : ContDiff ℝ 1 (cover u.val) :=
  (show ContDiff ℝ 2 (cover u.val) from u.property).of_le (by norm_num)
theorem c2_deriv_c1 (u : C2Coefficient) : ContDiff ℝ 1 (deriv (cover u.val)) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω)+1) (cover u.val) from u.property)).2.2
theorem periodic_deriv {f : ℝ→ℝ} (hp : Function.Periodic f 1) (hd : Differentiable ℝ f) : Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun y => f (y+1))=f := funext hp
  have h:=((hd (x+1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1)).deriv
  change deriv (fun y => f (y+1)) x=deriv f (x+1)*1 at h
  rw [he] at h
  simpa only [mul_one] using h.symm
noncomputable def derivativeCoefficient (f : Coefficient) (hf : ContDiff ℝ 1 (cover f)) : Coefficient where
  toFun := (periodic_deriv (cover_periodic f) (contDiff_one_iff_deriv.mp hf).1).lift
  continuous_toFun := (contDiff_one_iff_deriv.mp hf).2.quotient_liftOn' _
noncomputable def gradient (u : C2Coefficient) : Coefficient := derivativeCoefficient u.val (c2_c1 u)
noncomputable def flux (ρ : RegularDensity) (u : C2Coefficient) : Coefficient where
  toFun q := gradient u q/ρ.val.val q
  continuous_toFun := (gradient u).continuous.div ρ.val.val.continuous (density_ne ρ.val)
theorem flux_c1 (ρ : RegularDensity) (u : C2Coefficient) : ContDiff ℝ 1 (cover (flux ρ u)) :=
  (c2_deriv_c1 u).div ρ.property (fun x => density_ne ρ.val (x : CircleHodge.Circle))
/-- The actual continuous circle Laplacian δd, with the nonnegative geometer's sign. -/ noncomputable def laplacian (ρ : RegularDensity) (u : C2Coefficient) : Coefficient where
  toFun q := -(derivativeCoefficient (flux ρ u) (flux_c1 ρ u) q)/ρ.val.val q
  continuous_toFun := (derivativeCoefficient (flux ρ u) (flux_c1 ρ u)).continuous.neg.div
    ρ.val.val.continuous (density_ne ρ.val)
noncomputable def weightedMean (ρ : RegularDensity) (f : Coefficient) : ℝ := mean (ρ.val.val*f)
theorem weightedMean_sub (ρ : RegularDensity) (f g : Coefficient) : weightedMean ρ (f-g)=weightedMean ρ f-weightedMean ρ g := by
  unfold weightedMean
  rw [mul_sub,mean_sub]
theorem weightedMean_constant (ρ : RegularDensity) (c : ℝ) : weightedMean ρ (constant c)=c*mean ρ.val.val := by
  have he : ρ.val.val*constant c=c•ρ.val.val := by ext q;change _*c=c*_;ring
  rw [weightedMean,he,mean_smul]
noncomputable def constantC2 (c : ℝ) : C2Coefficient := ⟨constant c,by change ContDiff ℝ 2 (fun _ : ℝ => c);exact contDiff_const⟩
theorem gradient_sub (u v : C2Coefficient) : gradient (u-v)=gradient u-gradient v := ContinuousMap.ext fun q => Quotient.inductionOn q fun x =>
  deriv_sub ((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x) ((contDiff_one_iff_deriv.mp (c2_c1 v)).1 x)
theorem flux_sub (ρ : RegularDensity) (u v : C2Coefficient) : flux ρ (u-v)=flux ρ u-flux ρ v := ContinuousMap.ext fun q =>
  (congrArg (fun f : Coefficient => f q/ρ.val.val q) (gradient_sub u v)).trans (sub_div _ _ _)
theorem laplacian_sub (ρ : RegularDensity) (u v : C2Coefficient) : laplacian ρ (u-v)=laplacian ρ u-laplacian ρ v := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ (u-v))) x)/cover ρ.val.val x=_
  rw [flux_sub]
  change -(deriv (cover (flux ρ u)-cover (flux ρ v)) x)/cover ρ.val.val x=_
  rw [deriv_sub ((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x)
    ((contDiff_one_iff_deriv.mp (flux_c1 ρ v)).1 x)]
  change _=-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x-(-(deriv (cover (flux ρ v)) x)/cover ρ.val.val x)
  ring
theorem laplacian_of_constant (ρ : RegularDensity) (u : C2Coefficient) (c : ℝ) (hu : u.val=constant c) : laplacian ρ u=0 := by
  have hg : gradient u=0 := ContinuousMap.ext fun q => Quotient.inductionOn q fun x =>
    (congrArg (fun f : Coefficient => deriv (cover f) x) hu).trans (deriv_const x c)
  have hf : flux ρ u=0 := ContinuousMap.ext fun q =>
    (congrArg (fun f : Coefficient => f q/ρ.val.val q) hg).trans (zero_div _)
  exact ContinuousMap.ext fun q => Quotient.inductionOn q fun x => by
    change -(deriv (cover (flux ρ u)) x)/cover ρ.val.val x=0
    rw [hf]
    change -(deriv (fun _ : ℝ => (0 : ℝ)) x)/cover ρ.val.val x=0
    simp only [deriv_const,neg_zero,zero_div]
theorem weightedMean_laplacian (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (laplacian ρ u)=0 := by
  apply exact_mean_zero
  refine ⟨-flux ρ u,(flux_c1 ρ u).neg,fun x => ?_⟩
  have hd:=(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.neg).deriv
  change deriv (-cover (flux ρ u)) x=_
  rw [hd]
  change _=cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)
  field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]
theorem kernel_iff_constant (ρ : RegularDensity) (u : C2Coefficient) : laplacian ρ u=0 ↔ ∃ c : ℝ,u.val=constant c := by
  constructor
  · intro he
    have hz (x : ℝ) : deriv (cover (flux ρ u)) x=0 := by
      have h:=congrArg (fun f : Coefficient => cover f x) he
      change -(deriv (cover (flux ρ u)) x)/cover ρ.val.val x=0 at h
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right (density_ne ρ.val (x : CircleHodge.Circle)))
    have hc (x : ℝ) : cover (flux ρ u) x=cover (flux ρ u) 0 :=
      is_const_of_deriv_eq_zero (contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 hz x 0
    have hg : gradient u=(cover (flux ρ u) 0)•ρ.val.val := by
      ext q
      induction q using Quotient.inductionOn with | _ x =>
      exact (div_eq_iff (density_ne ρ.val (x : CircleHodge.Circle))).mp (hc x)
    have hm : mean (gradient u)=0 := exact_mean_zero ⟨u.val,c2_c1 u,fun _ => rfl⟩
    rw [hg,mean_smul] at hm
    have h0 : cover (flux ρ u) 0=0 := (mul_eq_zero.mp hm).resolve_right (ne_of_gt (mean_pos ρ.val))
    have hd (x : ℝ) : deriv (cover u.val) x=0 :=
      (congrArg (fun f : Coefficient => cover f x) hg).trans (by rw [h0,zero_smul];rfl)
    refine ⟨cover u.val 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero (contDiff_one_iff_deriv.mp (c2_c1 u)).1 hd x 0
  · rintro ⟨c,hc⟩;exact laplacian_of_constant ρ u c hc
noncomputable def potentialC2 (β : Coefficient) (hβ : ContDiff ℝ 1 (cover β)) : C2Coefficient := ⟨potential β,by
  change ContDiff ℝ ((1 : ℕ∞ω)+1) (cover (potential β))
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨(contDiff_one_iff_deriv.mp (potential_contDiff β)).1,by intro h;norm_num at h,?_⟩
  have he : deriv (cover (potential β))=fun x => cover β x-mean β := funext (potential_deriv β)
  rw [he]
  exact hβ.sub contDiff_const⟩
noncomputable def normalize (ρ : RegularDensity) (u : C2Coefficient) : C2Coefficient :=
  u-constantC2 (weightedMean ρ u.val/mean ρ.val.val)
theorem normalize_mean_zero (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (normalize ρ u).val=0 := by
  change weightedMean ρ (u.val-constant (weightedMean ρ u.val/mean ρ.val.val))=0
  rw [weightedMean_sub,weightedMean_constant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem normalize_laplacian (ρ : RegularDensity) (u : C2Coefficient) : laplacian ρ (normalize ρ u)=laplacian ρ u := by
  rw [normalize,laplacian_sub,laplacian_of_constant ρ (constantC2 (weightedMean ρ u.val/mean ρ.val.val)) _ rfl,sub_zero]
noncomputable def projectForcing (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  f-constant (weightedMean ρ f/mean ρ.val.val)
theorem project_mean_zero (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ (projectForcing ρ f)=0 := by
  rw [projectForcing,weightedMean_sub,weightedMean_constant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem project_eq_self (ρ : RegularDensity) (f : Coefficient) (h : weightedMean ρ f=0) : projectForcing ρ f=f := by
  ext q
  simp [projectForcing,constant,h]
noncomputable def firstPrimitive (ρ : RegularDensity) (f : Coefficient) : Coefficient := potential (ρ.val.val*f)
noncomputable def fluxConstant (ρ : RegularDensity) (f : Coefficient) : ℝ :=
  weightedMean ρ (firstPrimitive ρ f)/mean ρ.val.val
noncomputable def velocity (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  ρ.val.val*(constant (fluxConstant ρ f)-firstPrimitive ρ f)
theorem velocity_mean_zero (ρ : RegularDensity) (f : Coefficient) : mean (velocity ρ f)=0 := by
  change weightedMean ρ (constant (fluxConstant ρ f)-firstPrimitive ρ f)=0
  rw [weightedMean_sub,weightedMean_constant,fluxConstant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem velocity_c1 (ρ : RegularDensity) (f : Coefficient) : ContDiff ℝ 1 (cover (velocity ρ f)) :=
  ρ.property.mul (contDiff_const.sub (potential_contDiff (ρ.val.val*f)))
noncomputable def baseSolution (ρ : RegularDensity) (f : Coefficient) : C2Coefficient :=
  potentialC2 (velocity ρ f) (velocity_c1 ρ f)
theorem base_gradient (ρ : RegularDensity) (f : Coefficient) : gradient (baseSolution ρ f)=velocity ρ f := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change deriv (cover (potential (velocity ρ f))) x=cover (velocity ρ f) x
  simpa only [velocity_mean_zero,sub_zero] using potential_deriv (velocity ρ f) x
theorem base_flux (ρ : RegularDensity) (f : Coefficient) : flux ρ (baseSolution ρ f)=constant (fluxConstant ρ f)-firstPrimitive ρ f := by
  ext q
  change gradient (baseSolution ρ f) q/ρ.val.val q=fluxConstant ρ f-firstPrimitive ρ f q
  rw [base_gradient]
  change (ρ.val.val q*(fluxConstant ρ f-firstPrimitive ρ f q))/ρ.val.val q=_
  exact mul_div_cancel_left₀ _ (density_ne ρ.val q)
theorem firstPrimitive_hasDerivAt (ρ : RegularDensity) (f : Coefficient) (x : ℝ) : HasDerivAt (cover (firstPrimitive ρ f)) (cover ρ.val.val x*cover f x-weightedMean ρ f) x := realPotential_hasDerivAt (ρ.val.val*f) x
theorem base_solves (ρ : RegularDensity) (f : Coefficient) (h : weightedMean ρ f=0) : laplacian ρ (baseSolution ρ f)=f := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ (baseSolution ρ f))) x)/cover ρ.val.val x=cover f x
  rw [base_flux]
  change -(deriv ((fun _ : ℝ => fluxConstant ρ f)-cover (firstPrimitive ρ f)) x)/cover ρ.val.val x=cover f x
  rw [((hasDerivAt_const x (fluxConstant ρ f)).sub (firstPrimitive_hasDerivAt ρ f x)).deriv,h]
  simp only [sub_zero,zero_sub,neg_neg]
  exact mul_div_cancel_left₀ _ (density_ne ρ.val (x : CircleHodge.Circle))
/-- Constructed normalized Green solution to the forcing with its weighted constant projection removed. -/ noncomputable def green (ρ : RegularDensity) (f : Coefficient) : C2Coefficient :=
  normalize ρ (baseSolution ρ (projectForcing ρ f))
theorem green_solves_projected (ρ : RegularDensity) (f : Coefficient) : laplacian ρ (green ρ f)=projectForcing ρ f := by
  rw [green,normalize_laplacian]
  exact base_solves ρ _ (project_mean_zero ρ f)
theorem green_mean_zero (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ (green ρ f).val=0 := normalize_mean_zero _ _
theorem solutions_differ_constant (ρ : RegularDensity) (u v : C2Coefficient) : laplacian ρ u=laplacian ρ v ↔ ∃ c : ℝ,u.val-v.val=constant c := by
  change laplacian ρ u=laplacian ρ v ↔ ∃ c : ℝ,(u-v).val=constant c
  rw [← sub_eq_zero,← laplacian_sub,kernel_iff_constant]
theorem normalized_unique (ρ : RegularDensity) (u v : C2Coefficient) (he : laplacian ρ u=laplacian ρ v) (hu : weightedMean ρ u.val=0) (hv : weightedMean ρ v.val=0) : u=v := by
  obtain ⟨c,hc⟩:=(solutions_differ_constant ρ u v).mp he
  have hm : c*mean ρ.val.val=0 := by
    simpa only [weightedMean_sub,hu,hv,sub_self,weightedMean_constant] using (congrArg (weightedMean ρ) hc).symm
  exact Subtype.ext (sub_eq_zero.mp (hc.trans (by rw [(mul_eq_zero.mp hm).resolve_right (ne_of_gt (mean_pos ρ.val))];rfl)))
end ComputationalHodge.Poisson
namespace ComputationalHodge.GreenOperator
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals ComputationalPaths.Path.GeometricTopology MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
theorem norm_of_positive {x : ℝ} (hx : 0<x) : ‖x‖=x := (Real.norm_eq_abs x).trans (abs_of_pos hx)
theorem weightedMean_add (ρ : RegularDensity) (f g : Coefficient) : weightedMean ρ (f+g)=weightedMean ρ f+weightedMean ρ g := (congrArg mean (mul_add ρ.val.val f g)).trans
    (intervalIntegral.integral_add ((cover_continuous (ρ.val.val*f)).intervalIntegrable 0 1)
      ((cover_continuous (ρ.val.val*g)).intervalIntegrable 0 1))
theorem weightedMean_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) : weightedMean ρ (c•f)=c*weightedMean ρ f := by
  rw [weightedMean,mul_smul_comm,mean_smul]
  rfl
theorem weightedMean_bound (ρ : RegularDensity) (f : Coefficient) : ‖weightedMean ρ f‖≤mean ρ.val.val*‖f‖ := by
  rw [weightedMean,mean_circle]
  calc
    _ ≤ ∫ q : CircleHodge.Circle,‖ρ.val.val q*f q‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q : CircleHodge.Circle,ρ.val.val q*‖f‖ := integral_mono
      (continuous_integrable ((ρ.val.val.continuous.mul f.continuous).norm))
      (continuous_integrable (ρ.val.val.continuous.mul_const ‖f‖))
      (fun q => by rw [norm_mul,norm_of_positive (ρ.val.property q)];exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm q) (ρ.val.property q).le)
    _ = mean ρ.val.val*‖f‖ := by rw [integral_mul_const,← mean_circle]
/-- Actual continuous weighted-mean functional, bounded using the positive density integral. -/ noncomputable def meanFunctional (ρ : RegularDensity) : Coefficient →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    {toFun:=weightedMean ρ,map_add':=weightedMean_add ρ,map_smul':=fun c f => weightedMean_smul ρ c f}
    (mean ρ.val.val) (weightedMean_bound ρ)
/-- Closed subspace of continuous forcing with vanishing actual computational obstruction. -/ noncomputable def compatibleSpace (ρ : RegularDensity) : Submodule ℝ Coefficient := (meanFunctional ρ).ker
abbrev Compatible (ρ : RegularDensity) := ↥(compatibleSpace ρ)
theorem compatible_closed (ρ : RegularDensity) : IsClosed (compatibleSpace ρ : Set Coefficient) :=
  (meanFunctional ρ).isClosed_ker
instance compatible_complete (ρ : RegularDensity) : CompleteSpace (Compatible ρ) :=
  (compatible_closed ρ).completeSpace_coe
theorem compatible_iff_raw (ρ : RegularDensity) (f : Coefficient) : f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  ⟨fun h p => by rw [lineIntegral_eq_mean,show mean (ρ.val.val*f)=0 from h,zero_mul],
   fun h => by change mean (ρ.val.val*f)=0;simpa only [lineIntegral_unit] using h unitTrace⟩
/-- A quantitative actual primitive estimate; the bound is proved, not assumed for Green. -/ theorem potential_weight_bound (ρ : RegularDensity) (f : Coefficient) (hf : mean f=0) (C : ℝ) (hC : 0≤C) (h : ∀ q,‖f q‖≤C*ρ.val.val q) : ‖potential f‖≤C*mean ρ.val.val := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (mean_pos ρ.val).le)).mpr
  intro q
  let x := AddCircle.equivIco (1 : ℝ) 0 q
  have hx : (x : ℝ)∈Icc (0 : ℝ) 1 := ⟨x.property.1,by simpa using x.property.2.le⟩
  have hq : ((x : ℝ) : CircleHodge.Circle)=q := AddCircle.coe_equivIco
  rw [← hq]
  change ‖(∫ t in (0 : ℝ)..(x : ℝ),cover f t)-(x : ℝ)*mean f‖≤_
  rw [hf,mul_zero,sub_zero]
  exact (intervalIntegral.norm_integral_le_of_norm_le hx.1
      (Filter.Eventually.of_forall (fun t _ => h (t : CircleHodge.Circle)))
      ((continuous_const.mul (cover_continuous ρ.val.val)).intervalIntegrable 0 x)).trans
    ((intervalIntegral.integral_mono_interval (le_refl 0) hx.1 hx.2
      (Filter.Eventually.of_forall (fun t => mul_nonneg hC (ρ.val.property (t : CircleHodge.Circle)).le))
      ((continuous_const.mul (cover_continuous ρ.val.val)).intervalIntegrable 0 1)).trans_eq (intervalIntegral.integral_const_mul C _))
theorem primitive_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) : ‖firstPrimitive ρ f‖≤mean ρ.val.val*‖f‖ := by
  have h:=potential_weight_bound ρ (ρ.val.val*f) hf ‖f‖ (norm_nonneg f)
    (fun q => by
      rw [ContinuousMap.mul_apply,norm_mul,norm_of_positive (ρ.val.property q)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (f.norm_coe_le_norm q) (ρ.val.property q).le)
  simpa only [firstPrimitive,mul_comm] using h
theorem fluxConstant_bound (ρ : RegularDensity) (f : Coefficient) : ‖fluxConstant ρ f‖≤‖firstPrimitive ρ f‖ := by
  rw [fluxConstant,norm_div,norm_of_positive (mean_pos ρ.val)]
  exact (div_le_iff₀ (mean_pos ρ.val)).mpr (by simpa [mul_comm] using weightedMean_bound ρ (firstPrimitive ρ f))
theorem velocity_point_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) (q : CircleHodge.Circle) : ‖velocity ρ f q‖≤(2*mean ρ.val.val*‖f‖)*ρ.val.val q := by
  change ‖ρ.val.val q*(fluxConstant ρ f-firstPrimitive ρ f q)‖≤_
  rw [norm_mul,norm_of_positive (ρ.val.property q)]
  calc
    _ ≤ ρ.val.val q*(‖fluxConstant ρ f‖+‖firstPrimitive ρ f q‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (ρ.val.property q).le
    _ ≤ ρ.val.val q*(2*(mean ρ.val.val*‖f‖)) := mul_le_mul_of_nonneg_left
      (by linarith [primitive_bound ρ f hf,fluxConstant_bound ρ f,(firstPrimitive ρ f).norm_coe_le_norm q]) (ρ.val.property q).le
    _ = _ := by ring
theorem base_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) : ‖(baseSolution ρ f).val‖≤2*(mean ρ.val.val)^2*‖f‖ := by
  have h:=potential_weight_bound ρ (velocity ρ f) (velocity_mean_zero ρ f)
    (2*mean ρ.val.val*‖f‖) (mul_nonneg (mul_nonneg (by norm_num) (mean_pos ρ.val).le) (norm_nonneg f)) (velocity_point_bound ρ f hf)
  change ‖potential (velocity ρ f)‖≤_
  exact h.trans_eq (by ring)
theorem normalize_bound (ρ : RegularDensity) (u : C2Coefficient) : ‖(normalize ρ u).val‖≤2*‖u.val‖ := by
  have h : ‖weightedMean ρ u.val/mean ρ.val.val‖≤‖u.val‖ := by
    rw [norm_div,norm_of_positive (mean_pos ρ.val)]
    exact (div_le_iff₀ (mean_pos ρ.val)).mpr (by simpa [mul_comm] using weightedMean_bound ρ u.val)
  change ‖u.val-constant (weightedMean ρ u.val/mean ρ.val.val)‖≤_
  have hc : ‖constant (weightedMean ρ u.val/mean ρ.val.val)‖≤‖u.val‖ := (ContinuousMap.norm_le_of_nonempty _).mpr (fun _ => h)
  exact (norm_sub_le _ _).trans (by linarith)
theorem green_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) : ‖(green ρ f).val‖≤4*(mean ρ.val.val)^2*‖f‖ := by
  rw [green,project_eq_self ρ f hf]
  exact (normalize_bound ρ _).trans (by nlinarith [base_bound ρ f hf])
theorem gradient_smul (c : ℝ) (u : C2Coefficient) : gradient (c•u)=c•gradient u :=
  ContinuousMap.ext fun q => Quotient.inductionOn q fun x => (((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x).hasDerivAt.const_mul c).deriv
theorem flux_smul (ρ : RegularDensity) (c : ℝ) (u : C2Coefficient) : flux ρ (c•u)=c•flux ρ u :=
  ContinuousMap.ext fun q => (congrArg (fun f : Coefficient => f q/ρ.val.val q) (gradient_smul c u)).trans (mul_div_assoc c (gradient u q) (ρ.val.val q))
theorem laplacian_smul (ρ : RegularDensity) (c : ℝ) (u : C2Coefficient) : laplacian ρ (c•u)=c•laplacian ρ u := ContinuousMap.ext fun q => Quotient.inductionOn q fun x => by
  change -(deriv (cover (flux ρ (c•u))) x)/cover ρ.val.val x=_
  rw [flux_smul]
  change -(deriv (fun t => c*cover (flux ρ u) t) x)/cover ρ.val.val x=c*(-deriv (cover (flux ρ u)) x/cover ρ.val.val x)
  rw [(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.const_mul c).deriv]
  change -(c*deriv (cover (flux ρ u)) x)/cover ρ.val.val x=c*(-deriv (cover (flux ρ u)) x/cover ρ.val.val x)
  ring
theorem laplacian_add (ρ : RegularDensity) (u v : C2Coefficient) : laplacian ρ (u+v)=laplacian ρ u+laplacian ρ v := by
  have hn : laplacian ρ (-v) = -laplacian ρ v := by simpa only [show (-1 : ℝ)•v = -v from Subtype.ext (ContinuousMap.ext (fun q => neg_one_mul (v.val q))),neg_one_smul] using laplacian_smul ρ (-1) v
  simpa only [sub_neg_eq_add,hn] using laplacian_sub ρ u (-v)
noncomputable def solution (ρ : RegularDensity) (f : Compatible ρ) : C2Coefficient := green ρ f.val
theorem solution_solves (ρ : RegularDensity) (f : Compatible ρ) : laplacian ρ (solution ρ f)=f.val :=
  (green_solves_projected ρ f.val).trans (project_eq_self ρ f.val f.property)
theorem solution_mean_zero (ρ : RegularDensity) (f : Compatible ρ) : weightedMean ρ (solution ρ f).val=0 := green_mean_zero _ _
theorem solution_add (ρ : RegularDensity) (f g : Compatible ρ) : solution ρ (f+g)=solution ρ f+solution ρ g :=
  normalized_unique ρ _ _ (by rw [solution_solves,laplacian_add,solution_solves,solution_solves];rfl)
    (solution_mean_zero _ _) (by change weightedMean ρ ((solution ρ f).val+(solution ρ g).val)=0;rw [weightedMean_add,solution_mean_zero,solution_mean_zero,add_zero])
theorem solution_smul (ρ : RegularDensity) (c : ℝ) (f : Compatible ρ) : solution ρ (c•f)=c•solution ρ f :=
  normalized_unique ρ _ _ (by rw [solution_solves,laplacian_smul,solution_solves];rfl)
    (solution_mean_zero _ _) (by change weightedMean ρ (c•(solution ρ f).val)=0;rw [weightedMean_smul,solution_mean_zero,mul_zero])
/-- A bounded linear endomorphism of the actual closed C0 forcing subspace, with a C2 image. -/ noncomputable def greenMap (ρ : RegularDensity) : Compatible ρ →L[ℝ] Compatible ρ :=
  LinearMap.mkContinuous
    {toFun:=fun f => ⟨(solution ρ f).val,solution_mean_zero ρ f⟩,
     map_add':=fun f g => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_add ρ f g)),
     map_smul':=fun c f => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_smul ρ c f))}
    (4*(mean ρ.val.val)^2) (fun f => green_bound ρ f.val f.property)
theorem greenMap_bound (ρ : RegularDensity) (f : Compatible ρ) : ‖greenMap ρ f‖≤4*(mean ρ.val.val)^2*‖f‖ := green_bound ρ f.val f.property
theorem gradient_constant (c : ℝ) : gradient (constantC2 c)=0 := ContinuousMap.ext fun q => Quotient.inductionOn q fun x => deriv_const x c
theorem gradient_normalize (ρ : RegularDensity) (u : C2Coefficient) : gradient (normalize ρ u)=gradient u := by
  rw [Poisson.normalize,gradient_sub,gradient_constant,sub_zero]
theorem solution_gradient (ρ : RegularDensity) (f : Compatible ρ) : gradient (solution ρ f)=velocity ρ f.val := by
  rw [solution,green,project_eq_self ρ f.val f.property,gradient_normalize,base_gradient]
theorem greenMap_gradient_bound (ρ : RegularDensity) (f : Compatible ρ) : ‖gradient (solution ρ f)‖≤2*mean ρ.val.val*‖ρ.val.val‖*‖f‖ := by
  have hm := (mean_pos ρ.val).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  rw [solution_gradient]
  have hp : ρ.val.val q≤‖ρ.val.val‖ := by simpa only [norm_of_positive (ρ.val.property q)] using ρ.val.val.norm_coe_le_norm q
  exact (velocity_point_bound ρ f.val f.property q).trans
    ((mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*mean ρ.val.val*‖f.val‖)).trans_eq (by
      change (2*mean ρ.val.val*‖f.val‖)*‖ρ.val.val‖=2*mean ρ.val.val*‖ρ.val.val‖*‖f.val‖;ring))
end ComputationalHodge.GreenOperator
namespace ComputationalHodge.CompactGreen
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Filter Function Topology
open scoped Topology NNReal unitInterval ContDiff UniformConvergence
/-- The actual closed forcing ball for the inherited C0 supremum norm. -/ def forcingBall (ρ : RegularDensity) (B : ℝ) : Set (Compatible ρ) := {f | ‖f‖≤B}
/-- Actual Green images as continuous circle coefficients. -/ noncomputable def coefficientImage (ρ : RegularDensity) (B : ℝ) : Set Coefficient :=
  (fun f : Compatible ρ => (greenMap ρ f).val) '' forcingBall ρ B
noncomputable def valueBound (ρ : RegularDensity) (B : ℝ) : ℝ := 4*(mean ρ.val.val)^2*max 0 B
noncomputable def slopeBound (ρ : RegularDensity) (B : ℝ) : ℝ≥0 :=
  ⟨2*mean ρ.val.val*‖ρ.val.val‖*max 0 B,by have hm := (mean_pos ρ.val).le;positivity⟩
theorem image_value_bound (ρ : RegularDensity) (B : ℝ) {g : Coefficient} (hg : g∈coefficientImage ρ B) : ‖g‖≤valueBound ρ B := by
  obtain ⟨f,hf,rfl⟩:=hg
  exact (greenMap_bound ρ f).trans (mul_le_mul_of_nonneg_left
    (hf.trans (le_max_right 0 B)) (by positivity))
theorem cover_derivative_bound (ρ : RegularDensity) (B : ℝ) (f : forcingBall ρ B) (x : ℝ) : ‖deriv (cover (greenMap ρ f.val).val) x‖≤slopeBound ρ B := ((gradient (solution ρ f.val)).norm_coe_le_norm (x:CircleHodge.Circle)).trans ((greenMap_gradient_bound ρ f.val).trans
    (mul_le_mul_of_nonneg_left (f.property.trans (le_max_right 0 B))
      (mul_nonneg (mul_nonneg (by norm_num) (mean_pos ρ.val).le) (norm_nonneg ρ.val.val))))
theorem green_cover_lipschitz (ρ : RegularDensity) (B : ℝ) (f : forcingBall ρ B) : LipschitzWith (slopeBound ρ B) (cover (greenMap ρ f.val).val) :=
  lipschitzWith_of_nnnorm_deriv_le
    (fun x => (contDiff_one_iff_deriv.mp (c2_c1 (solution ρ f.val))).1 x)
    (cover_derivative_bound ρ B f)
theorem image_cover_equicontinuous (ρ : RegularDensity) (B : ℝ) : Equicontinuous (fun g : coefficientImage ρ B => cover g.val) := by
  apply Metric.equicontinuous_of_continuity_modulus
    (fun d : ℝ => (slopeBound ρ B : ℝ)*d)
    (by simpa only [id_eq,mul_zero] using (continuous_id.const_mul (slopeBound ρ B : ℝ)).tendsto (0 : ℝ))
  intro x y g
  obtain ⟨g,u,hu,rfl⟩:=g
  exact (green_cover_lipschitz ρ B ⟨u,hu⟩).dist_le_mul x y
theorem image_equicontinuous (ρ : RegularDensity) (B : ℝ) : Equicontinuous (fun g : coefficientImage ρ B => (g.val : CircleHodge.Circle → ℝ)) := equicontinuous_iff_continuous.mpr (isQuotientMap_quotient_mk'.continuous_iff.mpr
  (equicontinuous_iff_continuous.mp (image_cover_equicontinuous ρ B)))
theorem coefficient_ascoli (S : Set Coefficient) (C : ℝ) (hb : ∀ g∈S,‖g‖≤C) (he : Equicontinuous (fun g : S => (g.val : CircleHodge.Circle → ℝ))) : IsCompact (closure S) := by
  let e : Coefficient ≃ₜ BoundedContinuousFunction CircleHodge.Circle ℝ :=
    (ContinuousMap.equivBoundedOfCompact CircleHodge.Circle ℝ).toHomeomorphOfIsInducing
      (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact CircleHodge.Circle ℝ).isInducing
  let pull : (e '' S) → S := fun f => ⟨e.symm f.val,by
    obtain ⟨g,hg,hge⟩:=f.property
    rw [← hge,e.symm_apply_apply]
    exact hg⟩
  have hA : IsCompact (closure (e '' S)) := BoundedContinuousFunction.arzela_ascoli
    (Icc (-C) C) isCompact_Icc (e '' S)
    (fun f x hf => by
      obtain ⟨g,hg,rfl⟩:=hf
      change -C≤g x ∧ g x≤C
      exact abs_le.mp (by simpa only [Real.norm_eq_abs] using (g.norm_coe_le_norm x).trans (hb g hg)))
    (he.comp pull)
  exact (e.isClosedEmbedding.isCompact_preimage hA).closure_of_subset
    (fun g hg => subset_closure ⟨g,hg,rfl⟩)
theorem coefficientImage_precompact (ρ : RegularDensity) (B : ℝ) : IsCompact (closure (coefficientImage ρ B)) :=
  coefficient_ascoli _ (valueBound ρ B) (fun _ hg => image_value_bound ρ B hg) (image_equicontinuous ρ B)
/-- Bounded forcing gives a relatively compact family of actual Green solutions in H. -/ theorem green_ball_precompact (ρ : RegularDensity) (B : ℝ) : IsCompact (closure (greenMap ρ '' forcingBall ρ B)) := ((compatible_closed ρ).isClosedEmbedding_subtypeVal.isCompact_preimage
  (coefficientImage_precompact ρ B)).closure_of_subset
    (by rintro g ⟨f,hf,rfl⟩;exact subset_closure ⟨f,hf,rfl⟩)
theorem green_isCompactOperator (ρ : RegularDensity) : IsCompactOperator (greenMap ρ) := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (greenMap ρ)).mpr
  ⟨forcingBall ρ 1,(show forcingBall ρ 1=Metric.closedBall (0 : Compatible ρ) 1 from
    Set.ext (fun f => by rw [Metric.mem_closedBall,dist_zero_right];rfl)).symm ▸
      Metric.closedBall_mem_nhds _ zero_lt_one,green_ball_precompact ρ 1⟩
end ComputationalHodge.CompactGreen
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals
open MeasureTheory Set Function Topology Module
open scoped Topology NNReal unitInterval ContDiff
/-- Actual normalized twice continuously differentiable circle functions; no Banach claim. -/ abbrev Domain (ρ : RegularDensity) := {u : C2Coefficient // weightedMean ρ u.val=0}
noncomputable def laplaceData (ρ : RegularDensity) (u : Domain ρ) : Compatible ρ :=
  ⟨laplacian ρ u.val,weightedMean_laplacian ρ u.val⟩
noncomputable def liftData (ρ : RegularDensity) (f : Compatible ρ) : Domain ρ :=
  ⟨solution ρ f,solution_mean_zero ρ f⟩
noncomputable def reduced (ρ : RegularDensity) (μ : ℝ) : Compatible ρ →L[ℝ] Compatible ρ :=
  1-μ•greenMap ρ
noncomputable def shifted (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : Coefficient :=
  laplacian ρ u.val-μ•u.val.val
/-- Resonance is an actual nonzero normalized C2 solution, not an abstract assumption. -/ def Resonant (ρ : RegularDensity) (μ : ℝ) : Prop :=
  ∃ u : Domain ρ,u.val.val≠0 ∧ shifted ρ μ u=0
theorem lift_laplace (ρ : RegularDensity) (u : Domain ρ) : liftData ρ (laplaceData ρ u)=u :=
  Subtype.ext (normalized_unique ρ _ _ (solution_solves ρ (laplaceData ρ u))
    (solution_mean_zero ρ _) u.property)
theorem shifted_lift (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) : shifted ρ μ (liftData ρ f)=(reduced ρ μ f).val := congrArg (fun g : Coefficient => g-μ•(solution ρ f).val) (solution_solves ρ f)
theorem equation_iff (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) (f : Compatible ρ) : shifted ρ μ u=f.val ↔ reduced ρ μ (laplaceData ρ u)=f := by
  have he : shifted ρ μ u=(reduced ρ μ (laplaceData ρ u)).val := by
    rw [← shifted_lift,lift_laplace]
  rw [he]
  exact Subtype.ext_iff.symm
theorem eigen_to_resonant (ρ : RegularDensity) (μ : ℝ) (h : Module.End.HasEigenvalue (μ•greenMap ρ : Compatible ρ →L[ℝ] Compatible ρ).toLinearMap 1) : Resonant ρ μ := by
  obtain ⟨f,hf⟩ := h.exists_hasEigenvector
  have he : μ•greenMap ρ f=f := by simpa using hf.apply_eq_smul
  exact ⟨liftData ρ f,fun hz => hf.2 (he.symm.trans ((congrArg (fun g : Compatible ρ => μ•g) (Subtype.ext hz)).trans (smul_zero μ))),
    (shifted_lift ρ μ f).trans (sub_eq_zero.mpr (congrArg Subtype.val he).symm)⟩
/-- Stock compact-operator Fredholm theory is applied at nonzero spectral parameter1. -/ theorem reduced_bijective (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) : Function.Bijective (reduced ρ μ) := by
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (𝕜 := ℝ) (X := Compatible ρ) (T:=μ•greenMap ρ) ((green_isCompactOperator ρ).smul μ) (one_ne_zero : (1:ℝ)≠0) with he|hi
  · exact (h (eigen_to_resonant ρ μ he)).elim
  · rw [spectrum.mem_resolventSet_iff] at hi
    exact (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℝ) (E := Compatible ρ)).mp (by simpa [reduced] using hi)
noncomputable def reducedEquiv (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) : Compatible ρ ≃L[ℝ] Compatible ρ :=
  ContinuousLinearEquiv.ofBijective (𝕜 := ℝ) (𝕜' := ℝ) (E := Compatible ρ) (F := Compatible ρ) (reduced ρ μ)
    (LinearMap.ker_eq_bot.mpr (reduced_bijective ρ μ h).1)
    (LinearMap.range_eq_top.mpr (reduced_bijective ρ μ h).2)
theorem inverse_solves (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) (f : Compatible ρ) : reduced ρ μ ((reducedEquiv ρ μ h).symm f)=f :=
  (reducedEquiv ρ μ h).apply_symm_apply f
theorem unique_solvability (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) (f : Compatible ρ) : ∃! u : Domain ρ,shifted ρ μ u=f.val := ⟨liftData ρ ((reducedEquiv ρ μ h).symm f),
    (shifted_lift ρ μ _).trans (congrArg Subtype.val (inverse_solves ρ μ h f)),
    fun u hu => (lift_laplace ρ u).symm.trans (congrArg (liftData ρ)
      ((reduced_bijective ρ μ h).1 (((equation_iff ρ μ u f).mp hu).trans (inverse_solves ρ μ h f).symm)))⟩
end ComputationalHodge.CircleFredholm
namespace ComputationalHodge.FullCircleRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
/-- Actual geometer-sign operator on all C2 coefficients, without normalization. -/ noncomputable def fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u-μ•u.val
theorem fullShifted_sub (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) : fullShifted ρ μ (u-v)=fullShifted ρ μ u-fullShifted ρ μ v := (congrArg₂ (·-·) (laplacian_sub ρ u v) (smul_sub μ u.val v.val)).trans
    (sub_sub_sub_comm _ _ _ _)
end ComputationalHodge.FullCircleRange
namespace ComputationalHodge.PositiveResolvent
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm ComputationalHodge.FullCircleRange
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open MeasureTheory Set Function Filter Topology
open scoped Topology NNReal unitInterval ContDiff
/-- Necessary second-derivative sign at an actual local minimum. -/ theorem second_derivative_nonneg {f : ℝ → ℝ} {x : ℝ} (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := (Filter.Eventually.and hm (isLocalMax_of_deriv_deriv_neg (lt_of_not_ge hn) hm.deriv_eq_zero hc)).mono (fun _ hy => le_antisymm hy.2 hy.1)
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := he.deriv.mono (fun y hy => hy.trans (deriv_const y (f x)))
  exact (ne_of_lt (lt_of_not_ge hn)) (hd.deriv_eq.trans (deriv_const x 0))
/-- At a global minimum the literal geometer-sign weighted Laplacian is nonpositive. -/ theorem laplacian_at_min (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) (hm : ∀ q, u.val (x : CircleHodge.Circle) ≤ u.val q) : laplacian ρ u (x : CircleHodge.Circle) ≤ 0 := by
  have hl : IsLocalMin (cover u.val) x := Filter.Eventually.of_forall (fun y => hm (y : CircleHodge.Circle))
  have hdd := second_derivative_nonneg hl ((cover_continuous u.val).continuousAt)
  have hr := ρ.val.property (x : CircleHodge.Circle)
  change -(deriv (deriv (cover u.val)/cover ρ.val.val) x)/cover ρ.val.val x≤0
  rw [deriv_div ((contDiff_one_iff_deriv.mp (c2_deriv_c1 u)).1 x) ((contDiff_one_iff_deriv.mp ρ.property).1 x) (ne_of_gt hr),hl.deriv_eq_zero,zero_mul,sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (mul_nonneg hdd hr.le) (sq_nonneg _))) hr.le
/-- The actual unrestricted positive shift, with no equation or inverse assumed. -/ noncomputable def positive (ρ : RegularDensity) (κ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u+κ•u.val
theorem positive_eq_fullShifted (ρ : RegularDensity) (κ : ℝ) (u : C2Coefficient) : positive ρ κ u=fullShifted ρ (-κ) u := by
  simp only [positive,fullShifted,neg_smul,sub_neg_eq_add]
theorem positive_sub (ρ : RegularDensity) (κ : ℝ) (u v : C2Coefficient) : positive ρ κ (u-v)=positive ρ κ u-positive ρ κ v := by
  simp only [positive_eq_fullShifted,fullShifted_sub]
theorem positive_constant (ρ : RegularDensity) (κ c : ℝ) : positive ρ κ (constantC2 c)=constant (κ*c) := by
  rw [positive,laplacian_of_constant ρ (constantC2 c) c rfl,zero_add]
  rfl
theorem positive_zero (ρ : RegularDensity) (κ : ℝ) : positive ρ κ 0=0 :=
  (positive_constant ρ κ 0).trans (congrArg constant (mul_zero κ))
/-- Weak minimum principle on the actual compact weighted circle. -/ theorem minimum_principle (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u : C2Coefficient) (hf : ∀ q, 0≤positive ρ κ u q) : ∀ q, 0≤u.val q := by
  obtain ⟨q,_,hq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty u.val.continuous.continuousOn
  obtain ⟨x,rfl⟩ := Quotient.exists_rep q
  have hm : ∀ y, u.val (x : CircleHodge.Circle) ≤ u.val y := fun y => hq (Set.mem_univ y)
  have hl := laplacian_at_min ρ u x hm
  have hp := hf (x : CircleHodge.Circle)
  change 0≤laplacian ρ u (x : CircleHodge.Circle)+κ*u.val (x : CircleHodge.Circle) at hp
  have hn : 0≤u.val (x : CircleHodge.Circle) := by nlinarith
  exact fun y => hn.trans (hm y)
/-- Pointwise comparison for all actual C2 competitors, not just normalized functions. -/ theorem comparison (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u v : C2Coefficient) (h : ∀ q, positive ρ κ u q≤positive ρ κ v q) : ∀ q, u.val q≤v.val q := by
  have hp : ∀ q, 0≤positive ρ κ (v-u) q := by
    rw [positive_sub]
    exact fun q => sub_nonneg.mpr (h q)
  exact fun q => sub_nonneg.mp (minimum_principle ρ κ hκ (v-u) hp q)
theorem positive_injective (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : Injective (positive ρ κ) := fun u v h => Subtype.ext (ContinuousMap.ext (fun q =>
  le_antisymm (comparison ρ κ hκ u v (fun q => (congrArg (fun f : Coefficient => f q) h).le) q)
    (comparison ρ κ hκ v u (fun q => (congrArg (fun f : Coefficient => f q) h).symm.le) q)))
/-- Sharp density-independent supremum estimate, obtained by comparison with constants. -/ theorem supremum_bound (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (u : C2Coefficient) : ‖u.val‖ ≤ κ⁻¹*‖positive ρ κ u‖ := by
  let M : ℝ := ‖positive ρ κ u‖/κ
  have he : κ*M=‖positive ρ κ u‖ := by dsimp [M];rw [mul_comm,div_mul_cancel₀ _ hκ.ne']
  have hu : ∀ q,u.val q≤M := comparison ρ κ hκ u (constantC2 M) (fun q => by
    simpa only [positive_constant,constant,ContinuousMap.const_apply,he] using le_trans (le_abs_self _) ((positive ρ κ u).norm_coe_le_norm q))
  have hl : ∀ q,-M≤u.val q := comparison ρ κ hκ (constantC2 (-M)) u (fun q => by
    simpa only [positive_constant,constant,ContinuousMap.const_apply,mul_neg,he] using neg_le_of_abs_le ((positive ρ κ u).norm_coe_le_norm q))
  simpa only [M,div_eq_mul_inv,mul_comm] using (ContinuousMap.norm_le _ (div_nonneg (norm_nonneg _) hκ.le)).mpr (fun q => abs_le.mpr ⟨hl q,hu q⟩)
/-- Negative shifts have no actual normalized homogeneous mode. -/ theorem negative_nonresonant (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : ¬Resonant ρ (-κ) := by
  rintro ⟨u,hn,hu⟩
  have he : positive ρ κ u.val=positive ρ κ 0 :=
    (positive_eq_fullShifted ρ κ u.val).trans (hu.trans (positive_zero ρ κ).symm)
  exact hn (congrArg Subtype.val (positive_injective ρ κ hκ he))
/-- Actual existence for every continuous forcing, restoring the constant sector explicitly. -/ theorem exists_solution (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : ∃ u : C2Coefficient, positive ρ κ u=f := by
  obtain ⟨u,hu,_⟩ := unique_solvability ρ (-κ) (negative_nonresonant ρ κ hκ) ⟨projectForcing ρ f,project_mean_zero ρ f⟩
  refine ⟨u.val+constantC2 (κ⁻¹*(weightedMean ρ f/mean ρ.val.val)),?_⟩
  have he : positive ρ κ u.val=projectForcing ρ f := (positive_eq_fullShifted ρ κ u.val).trans hu
  have ha : κ*(κ⁻¹*(weightedMean ρ f/mean ρ.val.val))=weightedMean ρ f/mean ρ.val.val := by rw [← mul_assoc,mul_inv_cancel₀ hκ.ne',one_mul]
  rw [positive,laplacian_add,laplacian_of_constant ρ (constantC2 _) _ rfl]
  ext q
  have hq := congrArg (fun z : Coefficient => z q) he
  change laplacian ρ u.val q+κ*u.val.val q=f q-weightedMean ρ f/mean ρ.val.val at hq
  change laplacian ρ u.val q+0+κ*(u.val.val q+κ⁻¹*(weightedMean ρ f/mean ρ.val.val))=f q
  nlinarith
/-- An actual C2 solution chosen only after existence has been proved. -/ noncomputable def solve (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : C2Coefficient :=
  Classical.choose (exists_solution ρ κ hκ f)
theorem solve_equation (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : positive ρ κ (solve ρ κ hκ f)=f := Classical.choose_spec (exists_solution ρ κ hκ f)
theorem positive_add (ρ : RegularDensity) (κ : ℝ) (u v : C2Coefficient) : positive ρ κ (u+v)=positive ρ κ u+positive ρ κ v :=
  (congrArg₂ (·+·) (laplacian_add ρ u v) (smul_add κ u.val v.val)).trans (add_add_add_comm _ _ _ _)
theorem positive_smul (ρ : RegularDensity) (κ c : ℝ) (u : C2Coefficient) : positive ρ κ (c•u)=c•positive ρ κ u :=
  (congrArg₂ (·+·) (laplacian_smul ρ c u) (smul_comm κ c u.val)).trans (smul_add c _ _).symm
noncomputable def solveLinear (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : Coefficient →ₗ[ℝ] C2Coefficient where
  toFun := solve ρ κ hκ
  map_add' f g := positive_injective ρ κ hκ (by
    rw [solve_equation,positive_add,solve_equation,solve_equation])
  map_smul' c f := positive_injective ρ κ hκ (by
    rw [solve_equation,positive_smul,solve_equation]
    rfl)
/-- The full continuous-forcing solution operator; continuity is proved using comparison. -/ noncomputable def resolvent (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) : Coefficient →L[ℝ] Coefficient :=
  (C2Space.subtype.comp (solveLinear ρ κ hκ)).mkContinuous (κ⁻¹)
    (fun f => by
      change ‖(solve ρ κ hκ f).val‖≤κ⁻¹*‖f‖
      simpa only [solve_equation] using supremum_bound ρ κ hκ (solve ρ κ hκ f))
theorem resolvent_apply (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : resolvent ρ κ hκ f=(solve ρ κ hκ f).val := rfl
theorem resolvent_constant (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (c : ℝ) : resolvent ρ κ hκ (constant c)=constant (c/κ) := by
  change (solve ρ κ hκ (constant c)).val=(constantC2 (c/κ)).val
  apply congrArg Subtype.val
  apply positive_injective ρ κ hκ
  rw [solve_equation,positive_constant,mul_comm,div_mul_cancel₀ _ hκ.ne']
/-- The mean identity is a consequence of the literal solved differential equation. -/ theorem resolvent_weightedMean (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : weightedMean ρ (resolvent ρ κ hκ f)=weightedMean ρ f/κ := by
  rw [resolvent_apply]
  have he := congrArg (meanFunctional ρ) (solve_equation ρ κ hκ f)
  change weightedMean ρ (positive ρ κ (solve ρ κ hκ f))=weightedMean ρ f at he
  rw [positive,weightedMean_add,weightedMean_laplacian,weightedMean_smul,zero_add] at he
  apply (eq_div_iff hκ.ne').mpr
  simpa only [mul_comm] using he
end ComputationalHodge.PositiveResolvent
namespace ComputationalHodge.ResolventLimit
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.PositiveResolvent ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters Filter Set
open scoped Topology
/-- The scalar constant zero-mode, not an analytic one-form or a finite cochain. -/ noncomputable def harmonicPart (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  constant (weightedMean ρ f/mean ρ.val.val)
theorem harmonicPart_add (ρ : RegularDensity) (f g : Coefficient) : harmonicPart ρ (f+g)=harmonicPart ρ f+harmonicPart ρ g :=
  ContinuousMap.ext fun _ => (congrArg (fun x : ℝ => x/mean ρ.val.val) (weightedMean_add ρ f g)).trans (add_div _ _ _)
theorem harmonicPart_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) : harmonicPart ρ (c•f)=c•harmonicPart ρ f :=
  ContinuousMap.ext fun _ => (congrArg (fun x : ℝ => x/mean ρ.val.val) (weightedMean_smul ρ c f)).trans (mul_div_assoc _ _ _)
theorem harmonicPart_idempotent (ρ : RegularDensity) (f : Coefficient) : harmonicPart ρ (harmonicPart ρ f)=harmonicPart ρ f := by simp only [harmonicPart,weightedMean_constant,mul_div_cancel_right₀ _ (ne_of_gt (mean_pos ρ.val))]
theorem harmonicPart_zero_iff (ρ : RegularDensity) (f : Coefficient) : harmonicPart ρ f=0 ↔ weightedMean ρ f=0 :=
  ⟨fun h => (div_eq_zero_iff.mp (congrArg (fun z : Coefficient => z 0) h)).resolve_right (ne_of_gt (mean_pos ρ.val)),
    fun h => by ext q; simp [harmonicPart,h,constant]⟩
theorem harmonicPart_kernel (ρ : RegularDensity) (f : Coefficient) : laplacian ρ (constantC2 (weightedMean ρ f/mean ρ.val.val))=0 :=
  laplacian_of_constant ρ _ _ rfl
theorem harmonicPart_fixes_kernel (ρ : RegularDensity) (u : C2Coefficient) (hu : laplacian ρ u=0) : harmonicPart ρ u.val=u.val := by
  obtain ⟨c,hc⟩ := (kernel_iff_constant ρ u).mp hu
  rw [hc,harmonicPart,weightedMean_constant,mul_div_cancel_right₀ _ (ne_of_gt (mean_pos ρ.val))]
/-- The explicit bound for the already constructed compatible Green map. -/ noncomputable def greenConstant (ρ : RegularDensity) : ℝ := 4*(mean ρ.val.val)^2
theorem greenConstant_pos (ρ : RegularDensity) : 0<greenConstant ρ :=
  mul_pos (by norm_num) (sq_pos_of_pos (mean_pos ρ.val))
theorem solve_mean_zero (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (hf : weightedMean ρ f=0) : weightedMean ρ (solve ρ κ hκ f).val=0 :=
  (resolvent_weightedMean ρ κ hκ f).trans (by rw [hf,zero_div])
theorem solve_laplacian (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : laplacian ρ (solve ρ κ hκ f)=f-κ•(solve ρ κ hκ f).val :=
  eq_sub_of_add_eq (solve_equation ρ κ hκ f)
theorem green_recovers (ρ : RegularDensity) (u : C2Coefficient) (hu : weightedMean ρ u.val=0) : green ρ (laplacian ρ u)=u :=
  normalized_unique ρ _ _ ((green_solves_projected ρ _).trans (project_eq_self ρ _ (weightedMean_laplacian ρ u))) (green_mean_zero ρ _) hu
/-- Actual C2 normalization identifies the resolvent with a constructed Green solution. -/ theorem normalized_identity (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (hf : weightedMean ρ f=0) : solve ρ κ hκ f=green ρ (f-κ•resolvent ρ κ hκ f) := by
  simpa only [solve_laplacian,resolvent_apply] using (green_recovers ρ (solve ρ κ hκ f) (solve_mean_zero ρ κ hκ f hf)).symm
/-- Absorption gives a uniform compatible-sector estimate for small positive parameters. -/ theorem compatible_bound (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) (hf : weightedMean ρ f=0) : ‖resolvent ρ κ hκ f‖≤2*greenConstant ρ*‖f‖ := by
  have hM := (greenConstant_pos ρ).le
  have hz : weightedMean ρ (f-κ•resolvent ρ κ hκ f)=0 := by
    rw [weightedMean_sub,weightedMean_smul,resolvent_weightedMean,hf,zero_div,mul_zero,sub_self]
  have hb := green_bound ρ _ hz
  rw [← normalized_identity ρ κ hκ f hf] at hb
  change ‖resolvent ρ κ hκ f‖≤greenConstant ρ*‖f-κ•resolvent ρ κ hκ f‖ at hb
  have ht := norm_sub_le f (κ•resolvent ρ κ hκ f)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hκ] at ht
  have hp := mul_le_mul_of_nonneg_left ht hM
  have ha := mul_le_mul_of_nonneg_right hs (norm_nonneg (resolvent ρ κ hκ f))
  nlinarith
/-- The actual finite part has a quantitative C0 error tending to zero. -/ theorem compatible_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) (hf : weightedMean ρ f=0) : ‖resolvent ρ κ hκ f-(green ρ f).val‖≤2*κ*(greenConstant ρ)^2*‖f‖ := by
  let g : Compatible ρ := ⟨f,hf⟩
  let r : Compatible ρ := ⟨resolvent ρ κ hκ f,solve_mean_zero ρ κ hκ f hf⟩
  have he : resolvent ρ κ hκ f=(greenMap ρ (g-κ•r)).val := congrArg (fun u : C2Coefficient => u.val) (normalized_identity ρ κ hκ f hf)
  change ‖resolvent ρ κ hκ f-(greenMap ρ g).val‖≤_
  rw [he]
  simp only [map_sub,map_smul,Submodule.coe_sub,Submodule.coe_smul,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hκ]
  have hg : ‖(greenMap ρ r).val‖≤greenConstant ρ*‖resolvent ρ κ hκ f‖ := greenMap_bound ρ r
  nlinarith [mul_le_mul_of_nonneg_left hg hκ.le,
    mul_le_mul_of_nonneg_left (compatible_bound ρ κ hκ hs f hf) (mul_nonneg hκ.le (greenConstant_pos ρ).le)]
/-- Remove the true constant zero-mode singularity from the entire-forcing resolvent. -/ noncomputable def finitePart (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : Coefficient :=
  resolvent ρ κ hκ f-κ⁻¹•harmonicPart ρ f
theorem finitePart_eq_projected (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : finitePart ρ κ hκ f=resolvent ρ κ hκ (projectForcing ρ f) := by
  rw [projectForcing,map_sub,resolvent_constant]
  ext q
  change resolvent ρ κ hκ f q-κ⁻¹*(weightedMean ρ f/mean ρ.val.val)=
    resolvent ρ κ hκ f q-(weightedMean ρ f/mean ρ.val.val)/κ
  ring
theorem green_projected (ρ : RegularDensity) (f : Coefficient) : green ρ (projectForcing ρ f)=green ρ f :=
  congrArg (fun g : Coefficient => normalize ρ (baseSolution ρ g)) (project_eq_self ρ _ (project_mean_zero ρ f))
theorem finitePart_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) : ‖finitePart ρ κ hκ f-(green ρ f).val‖≤2*κ*(greenConstant ρ)^2*‖projectForcing ρ f‖ := by
  simpa only [finitePart_eq_projected,green_projected] using compatible_error ρ κ hκ hs (projectForcing ρ f) (project_mean_zero ρ f)
theorem scaled_decomposition (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : κ•resolvent ρ κ hκ f=harmonicPart ρ f+κ•finitePart ρ κ hκ f := by
  rw [finitePart,smul_sub,smul_smul,mul_inv_cancel₀ hκ.ne',one_smul]
  module
theorem residue_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) : ‖κ•resolvent ρ κ hκ f-harmonicPart ρ f‖≤2*κ*greenConstant ρ*‖projectForcing ρ f‖ := by
  rw [scaled_decomposition,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hκ,finitePart_eq_projected]
  exact (mul_le_mul_of_nonneg_left (compatible_bound ρ κ hκ hs _ (project_mean_zero ρ f)) hκ.le).trans_eq (by ring)
/-- Every positive parameter family tending to zero recovers the actual Green finite part in C0. -/ theorem finitePart_tendsto {α : Type*} {l : Filter α} (ρ : RegularDensity) (κ : α→ℝ) (hκ : ∀ a,0<κ a) (hlim : Tendsto κ l (𝓝 0)) (f : Coefficient) : Tendsto (fun a => finitePart ρ (κ a) (hκ a) f) l (𝓝 (green ρ f).val) := by
  have hs : ∀ᶠ a in l,κ a*greenConstant ρ≤1/2 :=
    ((hlim.mul_const (greenConstant ρ)).eventually (gt_mem_nhds (by norm_num))).mono (fun _ h => h.le)
  have hb : Tendsto (fun a => 2*κ a*(greenConstant ρ)^2*‖projectForcing ρ f‖) l (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (((tendsto_const_nhds.mul hlim).mul_const ((greenConstant ρ)^2)).mul_const ‖projectForcing ρ f‖)
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' (hs.mono (fun a ha => finitePart_error ρ (κ a) (hκ a) ha f)) hb)
/-- The scaled genuine resolvent converges in C0 to the scalar harmonic projection. -/ theorem residue_tendsto {α : Type*} {l : Filter α} (ρ : RegularDensity) (κ : α→ℝ) (hκ : ∀ a,0<κ a) (hlim : Tendsto κ l (𝓝 0)) (f : Coefficient) : Tendsto (fun a => κ a•resolvent ρ (κ a) (hκ a) f) l (𝓝 (harmonicPart ρ f)) := by
  simpa only [zero_smul,add_zero,← scaled_decomposition] using
    ((tendsto_const_nhds : Tendsto (fun _ : α => harmonicPart ρ f) l (𝓝 (harmonicPart ρ f))).add (hlim.smul (finitePart_tendsto ρ κ hκ hlim f)))
/-- Vanishing of the scalar residue is exactly the actual weighted based-loop obstruction. -/ theorem harmonicPart_zero_iff_raw (ρ : RegularDensity) (f : Coefficient) : harmonicPart ρ f=0 ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  (harmonicPart_zero_iff ρ f).trans (compatible_iff_raw ρ f)
theorem harmonicPart_zero_iff_cochain (ρ : RegularDensity) (f : Coefficient) : harmonicPart ρ f=0 ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := by
  simpa only [lineIntegral_fromTrace_harmonic] using harmonicPart_zero_iff_raw ρ f
/-- Every actual based-loop period is preserved by the scaled resolvent, for every positive parameter. -/ theorem scaled_resolvent_raw_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (p : Trace 0 0) : lineIntegral (ρ.val.val*(κ•resolvent ρ κ hκ f)) (fromTrace p)=lineIntegral (ρ.val.val*f) (fromTrace p) := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean]
  change weightedMean ρ (κ•resolvent ρ κ hκ f)*_=weightedMean ρ f*_
  rw [weightedMean_smul,resolvent_weightedMean,mul_div_cancel₀ _ hκ.ne']
theorem scaled_resolvent_cochain_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (p : Trace 0 0) : period p (meanHarmonic (ρ.val.val*(κ•resolvent ρ κ hκ f))).val=period p (meanHarmonic (ρ.val.val*f)).val := by
  simpa only [lineIntegral_fromTrace_harmonic] using scaled_resolvent_raw_period ρ κ hκ f p
end ComputationalHodge.ResolventLimit
