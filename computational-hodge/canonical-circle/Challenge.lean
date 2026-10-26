module
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearForm.Properties
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
  have hl : LipschitzWith K (fun x => f (min c x)) := by
    simpa only [Function.comp_def,id_eq,mul_one] using hf.comp (LipschitzWith.id.const_min c)
  have hr : LipschitzWith L (fun x => g (max c x)) := by
    simpa only [Function.comp_def,id_eq,mul_one] using hg.comp (LipschitzWith.id.const_max c)
  have hh : LipschitzWith (K+L) (fun x => f (min c x)+g (max c x)-f c) := by
    simpa only [Function.comp_def,one_mul,sub_eq_add_neg] using
      (isometry_add_right (-f c)).lipschitzWith.comp (hl.add hr)
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
  | trans p q hp hq =>
    obtain ⟨⟨K,hK⟩,⟨L,hL⟩⟩ := And.intro hp hq
    have hl : LipschitzWith (K*‖(2 : ℝ)‖₊) (fun x => rawLift p (2*x)) := by
      simpa only [Function.comp_def,add_zero] using hK.comp (affine_lipschitz 2 0)
    have hr : LipschitzWith (L*‖(2 : ℝ)‖₊) (fun x => rawLift q (2*x-1)) := by
      simpa only [Function.comp_def,sub_eq_add_neg] using hL.comp (affine_lipschitz 2 (-1))
    refine ⟨K*‖(2 : ℝ)‖₊+L*‖(2 : ℝ)‖₊,?_⟩
    exact cut_lipschitz hl (shift_lipschitz hr (rawLift p 1)) (by norm_num [rawLift_zero])
  | symm p hp =>
    obtain ⟨K,hK⟩ := hp
    have h : LipschitzWith (K*‖(-1 : ℝ)‖₊) (fun x => rawLift p (1-x)) := by
      simpa only [Function.comp_def,neg_one_mul,neg_add_eq_sub] using hK.comp (affine_lipschitz (-1) 1)
    refine ⟨K*‖(-1 : ℝ)‖₊,?_⟩
    change LipschitzWith (K*‖(-1 : ℝ)‖₊) (fun x => rawLift p (1-x)-rawLift p 1)
    simpa only [sub_eq_add_neg,add_comm] using shift_lipschitz h (-rawLift p 1)
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
theorem laplacian_smul (ρ : RegularDensity) (c : ℝ) (u : C2Coefficient) : laplacian ρ (c•u)=c•laplacian ρ u := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
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
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/ noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
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
theorem cover_derivative_bound (ρ : RegularDensity) (B : ℝ) (f : forcingBall ρ B) (x : ℝ) : ‖deriv (cover (greenMap ρ f.val).val) x‖≤slopeBound ρ B := by
  have hm := (mean_pos ρ.val).le
  calc
    _ = ‖gradient (solution ρ f.val) (x : CircleHodge.Circle)‖ := rfl
    _ ≤ ‖gradient (solution ρ f.val)‖ := (gradient (solution ρ f.val)).norm_coe_le_norm _
    _ ≤ 2*mean ρ.val.val*‖ρ.val.val‖*‖f.val‖ := greenMap_gradient_bound ρ f.val
    _ ≤ _ := mul_le_mul_of_nonneg_left (f.property.trans (le_max_right 0 B)) (by positivity)
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
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function Topology Module
open scoped Topology NNReal unitInterval ContDiff
noncomputable def reduced (ρ : RegularDensity) (μ : ℝ) : Compatible ρ →L[ℝ] Compatible ρ :=
  1-μ•greenMap ρ
end ComputationalHodge.CircleFredholm
namespace ComputationalHodge.ResonanceObstruction
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
theorem pairing_comm (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=pairing ρ g f := congrArg mean (mul_right_comm ρ.val.val f g)
theorem pairing_sub_left (ρ : RegularDensity) (f g h : Coefficient) : pairing ρ (f-g) h=pairing ρ f h-pairing ρ g h := by
  unfold pairing
  rw [mul_sub,sub_mul,mean_sub]
theorem pairing_smul_left (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) : pairing ρ (c•f) g=c*pairing ρ f g := by
  unfold pairing
  rw [mul_smul_comm,smul_mul_assoc,mean_smul]
theorem pairing_smul_right (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) : pairing ρ f (c•g)=c*pairing ρ f g := by
  rw [pairing_comm,pairing_smul_left,pairing_comm ρ g f]
theorem pairing_positive (ρ : RegularDensity) (f : Coefficient) (hf : f≠0) : 0<pairing ρ f f := by
  obtain ⟨q,hq⟩ : ∃ q,f q≠0 := by simpa using DFunLike.exists_ne hf
  rw [pairing,mean_circle]
  exact integral_pos_of_integrable_nonneg_nonzero (ρ.val.val*f*f).continuous
    (continuous_integrable (ρ.val.val*f*f).continuous)
    (fun t => by change 0≤ρ.val.val t*f t*f t;simpa only [mul_assoc] using mul_nonneg (ρ.val.property t).le (mul_self_nonneg (f t)))
    (show ρ.val.val q*f q*f q≠0 from mul_ne_zero (mul_ne_zero (density_ne ρ.val q) hq) hq)
end ComputationalHodge.ResonanceObstruction
namespace ComputationalHodge.FullCircleRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
/-- Actual geometer-sign operator on all C2 coefficients, without normalization. -/ noncomputable def fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u-μ•u.val
theorem fullShifted_sub (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) : fullShifted ρ μ (u-v)=fullShifted ρ μ u-fullShifted ρ μ v := (congrArg₂ (·-·) (laplacian_sub ρ u v) (smul_sub μ u.val v.val)).trans
    (sub_sub_sub_comm _ _ _ _)
theorem fullShifted_constant (ρ : RegularDensity) (μ c : ℝ) : fullShifted ρ μ (constantC2 c)=constant (-μ*c) := by
  rw [fullShifted,laplacian_of_constant ρ (constantC2 c) c rfl]
  ext q
  change (0 : ℝ)-μ*c=(-μ)*c
  ring
theorem weightedMean_fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : weightedMean ρ (fullShifted ρ μ u)= -μ*weightedMean ρ u.val := by
  rw [fullShifted,weightedMean_sub,weightedMean_laplacian,weightedMean_smul]
  ring
theorem nonzero_homogeneous_normalized (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) (v : C2Coefficient) (hv : fullShifted ρ μ v=0) : weightedMean ρ v.val=0 := by
  exact (mul_eq_zero.mp ((weightedMean_fullShifted ρ μ v).symm.trans
    ((congrArg (meanFunctional ρ) hv).trans (map_zero _)))).resolve_left (neg_ne_zero.mpr hμ)
theorem pairing_constant_left (ρ : RegularDensity) (a : ℝ) (v : Coefficient) : pairing ρ (constant a) v=a*weightedMean ρ v := by
  have h : ρ.val.val*constant a*v=a•(ρ.val.val*v) := by ext q;change _*a*_ = a*(_*_);ring
  change mean (ρ.val.val*constant a*v)=a*mean (ρ.val.val*v)
  rw [h,mean_smul]
theorem pairing_one_right (ρ : RegularDensity) (f : Coefficient) : pairing ρ f (constant 1)=weightedMean ρ f := by
  rw [pairing_comm,pairing_constant_left,one_mul]
theorem zero_solvable_iff_raw (ρ : RegularDensity) (f : Coefficient) : (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := ⟨fun ⟨u,hu⟩ => (compatible_iff_raw ρ f).mp
    (by change weightedMean ρ f=0;rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]),
   fun hp => let g : Compatible ρ := ⟨f,(compatible_iff_raw ρ f).mpr hp⟩
     ⟨solution ρ g,by simpa only [fullShifted,zero_smul,sub_zero] using solution_solves ρ g⟩⟩
end ComputationalHodge.FullCircleRange
namespace ComputationalHodge.CanonicalCircle
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.FullCircleRange ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function
open scoped Topology NNReal unitInterval ContDiff
/-- The actual unrestricted scalar circle Laplacian as an algebraic linear map. -/ noncomputable def laplaceMap (ρ : RegularDensity) : C2Coefficient →ₗ[ℝ] Coefficient where
  toFun := laplacian ρ
  map_add' := laplacian_add ρ
  map_smul' := laplacian_smul ρ
/-- The shifted differential expression on every actual C2 coefficient. -/ noncomputable def operator (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] Coefficient :=
  laplaceMap ρ-μ•C2Space.subtype
/-- Actual homogeneous C2 solutions, with no external finite-dimensionality assumption. -/ noncomputable def homogeneousSpace (ρ : RegularDensity) (μ : ℝ) : Submodule ℝ C2Coefficient :=
  (operator ρ μ).ker
abbrev Homogeneous (ρ : RegularDensity) (μ : ℝ) := ↥(homogeneousSpace ρ μ)
noncomputable def reducedModes (ρ : RegularDensity) (μ : ℝ) : Submodule ℝ (Compatible ρ) :=
  (reduced ρ μ).ker
theorem reduced_fixed (ρ : RegularDensity) (μ : ℝ) (x : reducedModes ρ μ) : μ•greenMap ρ x.val=x.val :=
  (sub_eq_zero.mp (show x.val-μ•greenMap ρ x.val=0 from x.property)).symm
theorem reduced_modes_finite (ρ : RegularDensity) (μ : ℝ) : FiniteDimensional ℝ (reducedModes ρ μ) := by
  let A : Compatible ρ →ₗ[ℝ] Compatible ρ := (μ•greenMap ρ).toLinearMap
  have hpres : ∀ x∈reducedModes ρ μ,A x∈reducedModes ρ μ := by
    intro x hx
    have he : A x=x := reduced_fixed ρ μ ⟨x,hx⟩
    rw [he]
    exact hx
  have hc : IsCompactOperator A := (green_isCompactOperator ρ).smul μ
  have hr := hc.restrict hpres (ContinuousLinearMap.isClosed_ker (reduced ρ μ))
  have he : (A.restrict hpres : reducedModes ρ μ → reducedModes ρ μ)=id := by
    funext x
    apply Subtype.ext
    exact reduced_fixed ρ μ x
  exact FiniteDimensional.of_isCompactOperator_id (he ▸ hr)
theorem green_recovers (ρ : RegularDensity) (u : C2Coefficient) (hu : weightedMean ρ u.val=0) : solution ρ ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩=u :=
  normalized_unique ρ _ u (solution_solves ρ _) (solution_mean_zero ρ _) hu
noncomputable def laplaceCompatible (ρ : RegularDensity) : C2Coefficient →ₗ[ℝ] Compatible ρ where
  toFun u := ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩
  map_add' u v := Subtype.ext (laplacian_add ρ u v)
  map_smul' c u := Subtype.ext (laplacian_smul ρ c u)
noncomputable def kernelTransfer (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) : Homogeneous ρ μ →ₗ[ℝ] reducedModes ρ μ where
  toFun u := ⟨laplaceCompatible ρ u.val,by
    apply Subtype.ext
    exact (congrArg (fun v : C2Coefficient => laplacian ρ u.val-μ•v.val)
      (green_recovers ρ u.val (nonzero_homogeneous_normalized ρ μ hμ u.val u.property))).trans u.property⟩
  map_add' u v := Subtype.ext (Subtype.ext (laplacian_add ρ u.val v.val))
  map_smul' c u := Subtype.ext (Subtype.ext (laplacian_smul ρ c u.val))
theorem kernelTransfer_injective (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) : Injective (kernelTransfer ρ μ hμ) := fun u v h =>
  Subtype.ext (normalized_unique ρ u.val v.val
    (show laplacian ρ u.val=laplacian ρ v.val from congrArg (fun x : reducedModes ρ μ => x.val.val) h)
    (nonzero_homogeneous_normalized ρ μ hμ u.val u.property)
    (nonzero_homogeneous_normalized ρ μ hμ v.val v.property))
theorem homogeneous_finite (ρ : RegularDensity) (μ : ℝ) : FiniteDimensional ℝ (Homogeneous ρ μ) := by
  by_cases hμ : μ=0
  · subst μ
    let E : Homogeneous ρ 0 →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.val.val 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective (V₂ := ℝ) E ?_
    intro u v h
    have hu : fullShifted ρ 0 u.val=0 := u.property
    have hv : fullShifted ρ 0 v.val=0 := v.property
    obtain ⟨a,ha⟩ := (kernel_iff_constant ρ u.val).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hu)
    obtain ⟨b,hb⟩ := (kernel_iff_constant ρ v.val).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hv)
    have hab : a=b := by change u.val.val 0=v.val.val 0 at h;simpa only [ha,hb,constant,ContinuousMap.const_apply] using h
    exact Subtype.ext (Subtype.ext (ha.trans ((congrArg constant hab).trans hb.symm)))
  · have := reduced_modes_finite ρ μ
    exact FiniteDimensional.of_injective (V₂ := reducedModes ρ μ) (kernelTransfer ρ μ hμ) (kernelTransfer_injective ρ μ hμ)
theorem pairing_eq_weightedMean (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=weightedMean ρ (f*g) := congrArg mean (mul_assoc ρ.val.val f g)
theorem pairing_add_left (ρ : RegularDensity) (f g h : Coefficient) : pairing ρ (f+g) h=pairing ρ f h+pairing ρ g h := by
  simp only [pairing_eq_weightedMean,add_mul,weightedMean_add]
theorem pairing_add_right (ρ : RegularDensity) (f g h : Coefficient) : pairing ρ f (g+h)=pairing ρ f g+pairing ρ f h := by
  rw [pairing_comm ρ f (g+h),pairing_add_left,pairing_comm ρ g f,pairing_comm ρ h f]
noncomputable def massForm (ρ : RegularDensity) : LinearMap.BilinForm ℝ C2Coefficient where
  toFun u :=
    { toFun := fun v => pairing ρ u.val v.val
      map_add' := fun v w => pairing_add_right ρ u.val v.val w.val
      map_smul' := fun c v => pairing_smul_right ρ c u.val v.val }
  map_add' u v := LinearMap.ext fun w => pairing_add_left ρ u.val v.val w.val
  map_smul' c u := LinearMap.ext fun v => pairing_smul_left ρ c u.val v.val
noncomputable def gram (ρ : RegularDensity) (μ : ℝ) : LinearMap.BilinForm ℝ (Homogeneous ρ μ) :=
  (massForm ρ).restrict (homogeneousSpace ρ μ)
theorem gram_nondegenerate (ρ : RegularDensity) (μ : ℝ) : (gram ρ μ).Nondegenerate := by
  have hz : ∀ u : Homogeneous ρ μ,gram ρ μ u u=0 → u=0 := fun u h =>
    Classical.byContradiction fun hn =>
      (ne_of_gt (pairing_positive ρ u.val.val (fun he => hn (Subtype.ext (Subtype.ext he))))) h
  exact ⟨fun u hu => hz u (hu u),fun u hu => hz u (hu u)⟩
noncomputable def kernelFunctional (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] Module.Dual ℝ (Homogeneous ρ μ) where
  toFun u := (massForm ρ u).comp (homogeneousSpace ρ μ).subtype
  map_add' u v := LinearMap.ext fun k => pairing_add_left ρ u.val v.val k.val.val
  map_smul' c u := LinearMap.ext fun k => pairing_smul_left ρ c u.val k.val.val
noncomputable def gramEquiv (ρ : RegularDensity) (μ : ℝ) : Homogeneous ρ μ ≃ₗ[ℝ] Module.Dual ℝ (Homogeneous ρ μ) := by
  letI := homogeneous_finite ρ μ
  exact LinearMap.BilinForm.toDual (K := ℝ) (V := Homogeneous ρ μ) (gram ρ μ) (gram_nondegenerate ρ μ)
/-- Finite Gram projection into the actual homogeneous C2 kernel. -/ noncomputable def kernelProjector (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] C2Coefficient :=
  (homogeneousSpace ρ μ).subtype.comp ((gramEquiv ρ μ).symm.toLinearMap.comp (kernelFunctional ρ μ))
theorem projector_mem (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : kernelProjector ρ μ u∈homogeneousSpace ρ μ := ((gramEquiv ρ μ).symm (kernelFunctional ρ μ u)).property
theorem projector_pairing (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) (k : Homogeneous ρ μ) : pairing ρ (kernelProjector ρ μ u).val k.val.val=pairing ρ u.val k.val.val :=
  congrArg (fun f : Module.Dual ℝ (Homogeneous ρ μ) => f k)
    ((gramEquiv ρ μ).apply_symm_apply (kernelFunctional ρ μ u))
noncomputable def canonicalizer (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] C2Coefficient :=
  LinearMap.id-kernelProjector ρ μ
def OrthogonalToKernel (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Prop :=
  ∀ v : C2Coefficient,fullShifted ρ μ v=0 → pairing ρ u.val v.val=0
theorem canonicalizer_preserves (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : fullShifted ρ μ (canonicalizer ρ μ u)=fullShifted ρ μ u := by
  change operator ρ μ (u-kernelProjector ρ μ u)=operator ρ μ u
  rw [map_sub,show operator ρ μ (kernelProjector ρ μ u)=0 from projector_mem ρ μ u,sub_zero]
theorem canonicalizer_orthogonal (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : OrthogonalToKernel ρ μ (canonicalizer ρ μ u) := fun v hv =>
  (pairing_sub_left ρ u.val (kernelProjector ρ μ u).val v.val).trans
    (sub_eq_zero.mpr (projector_pairing ρ μ u ⟨v,hv⟩).symm)
theorem orthogonal_unique (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (h : fullShifted ρ μ u=fullShifted ρ μ v) (hu : OrthogonalToKernel ρ μ u) (hv : OrthogonalToKernel ρ μ v) : u=v := by
  have hd : fullShifted ρ μ (u-v)=0 := (fullShifted_sub ρ μ u v).trans (sub_eq_zero.mpr h)
  have hz : pairing ρ (u-v).val (u-v).val=0 := by
    change pairing ρ (u.val-v.val) (u-v).val=0
    rw [pairing_sub_left,hu (u-v) hd,hv (u-v) hd,sub_self]
  by_contra hn
  have hne : (u-v).val≠0 := fun he => hn (sub_eq_zero.mp (Subtype.ext he))
  exact (ne_of_gt (pairing_positive ρ (u-v).val hne)) hz
theorem canonicalizer_independent (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (h : fullShifted ρ μ u=fullShifted ρ μ v) : canonicalizer ρ μ u=canonicalizer ρ μ v :=
  orthogonal_unique ρ μ _ _ ((canonicalizer_preserves ρ μ u).trans (h.trans (canonicalizer_preserves ρ μ v).symm))
    (canonicalizer_orthogonal ρ μ u) (canonicalizer_orthogonal ρ μ v)
/-- Every solvable actual equation has one kernel-orthogonal actual C2 representative. -/ theorem solvable_iff_unique_orthogonal (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) : (∃ u : C2Coefficient,fullShifted ρ μ u=f) ↔ ∃! u : C2Coefficient,fullShifted ρ μ u=f ∧ OrthogonalToKernel ρ μ u :=
  ⟨fun ⟨u,hu⟩ => ⟨canonicalizer ρ μ u,⟨(canonicalizer_preserves ρ μ u).trans hu,canonicalizer_orthogonal ρ μ u⟩,
    fun v hv => orthogonal_unique ρ μ v (canonicalizer ρ μ u) (hv.1.trans ((canonicalizer_preserves ρ μ u).trans hu).symm) hv.2 (canonicalizer_orthogonal ρ μ u)⟩,
   fun ⟨u,hu,_⟩ => ⟨u,hu.1⟩⟩
/-- Weighted L2 mass: the integral of rho times the squared actual function. -/ noncomputable def mass (ρ : RegularDensity) (u : C2Coefficient) : ℝ := pairing ρ u.val u.val
theorem mass_zero (ρ : RegularDensity) : mass ρ 0=0 := by
  simpa only [mass,Submodule.coe_zero,sub_self] using pairing_sub_left ρ 0 0 0
theorem mass_nonneg (ρ : RegularDensity) (u : C2Coefficient) : 0≤mass ρ u :=
  (eq_or_ne u 0).elim (fun hu => le_of_eq ((congrArg (mass ρ) hu).trans (mass_zero ρ)).symm)
    (fun hu => (pairing_positive ρ u.val (fun he => hu (Subtype.ext he))).le)
theorem mass_eq_zero_iff (ρ : RegularDensity) (u : C2Coefficient) : mass ρ u=0 ↔ u=0 :=
  ⟨fun h => Classical.byContradiction fun hu =>
    (ne_of_gt (pairing_positive ρ u.val (fun he => hu (Subtype.ext he)))) h,
   fun hu => hu ▸ mass_zero ρ⟩
theorem canonicalizer_idempotent (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : canonicalizer ρ μ (canonicalizer ρ μ u)=canonicalizer ρ μ u :=
  orthogonal_unique ρ μ _ _ (canonicalizer_preserves ρ μ (canonicalizer ρ μ u))
    (canonicalizer_orthogonal ρ μ (canonicalizer ρ μ u)) (canonicalizer_orthogonal ρ μ u)
/-- Pythagoras for weighted L2 mass along the actual solution coset. -/ theorem mass_pythagorean (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient) (h : fullShifted ρ μ w=fullShifted ρ μ u) : mass ρ w=mass ρ (canonicalizer ρ μ u)+mass ρ (w-canonicalizer ρ μ u) := by
  let c:=canonicalizer ρ μ u
  have hd : fullShifted ρ μ (w-c)=0 :=
    (fullShifted_sub ρ μ w c).trans (sub_eq_zero.mpr (h.trans (canonicalizer_preserves ρ μ u).symm))
  have hc : pairing ρ c.val (w-c).val=0 := canonicalizer_orthogonal ρ μ u (w-c) hd
  have hw : w=c+(w-c) := by abel
  conv_lhs => rw [hw]
  change pairing ρ (c.val+(w-c).val) (c.val+(w-c).val)=pairing ρ c.val c.val+pairing ρ (w-c).val (w-c).val
  rw [pairing_add_left,pairing_add_right,pairing_add_right,hc,pairing_comm ρ (w-c).val c.val,hc]
  ring
theorem mass_minimum (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient) (h : fullShifted ρ μ w=fullShifted ρ μ u) : mass ρ (canonicalizer ρ μ u)≤mass ρ w :=
  (le_add_of_nonneg_right (mass_nonneg ρ (w-canonicalizer ρ μ u))).trans (mass_pythagorean ρ μ u w h).symm.le
theorem mass_minimum_equality (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient) (h : fullShifted ρ μ w=fullShifted ρ μ u) : mass ρ w=mass ρ (canonicalizer ρ μ u) ↔ w=canonicalizer ρ μ u := by
  rw [mass_pythagorean ρ μ u w h,add_eq_left,mass_eq_zero_iff,sub_eq_zero]
theorem zero_orthogonal_iff_mean (ρ : RegularDensity) (u : C2Coefficient) : OrthogonalToKernel ρ 0 u ↔ weightedMean ρ u.val=0 := by
  constructor
  · intro hu
    have hc : fullShifted ρ 0 (constantC2 1)=0 := by rw [fullShifted_constant];ext q;simp [constant]
    simpa only [Poisson.constantC2,pairing_one_right] using hu (constantC2 1) hc
  · intro hu v hv
    obtain ⟨c,hc⟩ := (kernel_iff_constant ρ v).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hv)
    rw [hc,pairing_comm,pairing_constant_left,hu,mul_zero]
theorem canonicalizer_zero_eq_normalize (ρ : RegularDensity) (u : C2Coefficient) : canonicalizer ρ 0 u=normalize ρ u := by
  have hn : fullShifted ρ 0 (normalize ρ u)=fullShifted ρ 0 u := by
    simpa only [fullShifted,zero_smul,sub_zero] using normalize_laplacian ρ u
  exact orthogonal_unique ρ 0 _ _ ((canonicalizer_preserves ρ 0 u).trans hn.symm)
    (canonicalizer_orthogonal ρ 0 u) ((zero_orthogonal_iff_mean ρ _).mpr (normalize_mean_zero ρ u))
/-- Literal computational-trace compatibility is equivalent to one canonical actual C2 solution. -/ theorem zero_raw_iff_unique (ρ : RegularDensity) (f : Coefficient) : (∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0) ↔ ∃! u : C2Coefficient,fullShifted ρ 0 u=f ∧ OrthogonalToKernel ρ 0 u :=
  (zero_solvable_iff_raw ρ f).symm.trans (solvable_iff_unique_orthogonal ρ 0 f)
theorem zero_cochain_iff_unique (ρ : RegularDensity) (f : Coefficient) : (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0) ↔ ∃! u : C2Coefficient,fullShifted ρ 0 u=f ∧ OrthogonalToKernel ρ 0 u := by
  simpa only [lineIntegral_fromTrace_harmonic] using zero_raw_iff_unique ρ f
theorem canonicalizer_zero_green (ρ : RegularDensity) (f : Coefficient) (u : C2Coefficient) (hu : fullShifted ρ 0 u=f) : canonicalizer ρ 0 u=green ρ f := by
  have hm : weightedMean ρ f=0 := by rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]
  have hg : fullShifted ρ 0 (green ρ f)=f := by
    simpa only [fullShifted,zero_smul,sub_zero,project_eq_self ρ f hm] using green_solves_projected ρ f
  exact orthogonal_unique ρ 0 _ _ ((canonicalizer_preserves ρ 0 u).trans (hu.trans hg.symm))
    (canonicalizer_orthogonal ρ 0 u) ((zero_orthogonal_iff_mean ρ _).mpr (green_mean_zero ρ f))
end ComputationalHodge.CanonicalCircle
