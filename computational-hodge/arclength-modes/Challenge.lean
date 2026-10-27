module
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
@[expose] public section
/-
Copyright (c) 2025 Computational Paths contributors.
Upstream excerpts are MIT licensed; see SOURCE-LICENSE.txt.
Ported at the exact revision recorded in source-provenance.json.
-/
/-! Minimal literal source port of the user's endpoint-changing trace and scoped
rewrite definitions. Only imports, module visibility and enclosing namespaces
are adapted. No claim about equality-indexed raw Path or HoTT is made. -/
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
/-- The actual signed integral of edge coefficients along a computational trace. -/
def period {S : GeometricStepSystem A E} {a b : A} : GeometricTrace S a b → Cochain E →ₗ[ℝ] ℝ
  | .refl _ => 0
  | .single e => evaluation e
  | .trans p q => period p + period q
  | .symm p => -period p
/-- The degree-zero coboundary, with actual source and target evaluations. -/
def d0 (S : GeometricStepSystem A E) : (A → ℝ) →ₗ[ℝ] Cochain E where
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
/-- All named rules, including their endpoints: no unlisted-rule assumption. -/
structure Cell (P : ScopedGeometricRewritePresentation S) where
  src : A
  tgt : A
  left : GeometricTrace S.toGeometricStepSystem src tgt
  right : GeometricTrace S.toGeometricStepSystem src tgt
  rule : P.rule left right
/-- The next coboundary evaluates every named relation's actual period difference. -/
def d1 (P : ScopedGeometricRewritePresentation S) : Cochain E →ₗ[ℝ] (Cell P → ℝ) :=
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
/-- Complete geometric relations are actual endpoint-fixed path homotopies. -/
noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) : ScopedGeometricRewritePresentation S where
  rule p q := _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule h := h
end ComputationalHodge.LoopCharacters
namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
open scoped unitInterval
/-- The ordinary covering of the unit additive circle by the real line. -/
theorem circleCover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
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
/-- One actual circle loop as a finite computational generator. -/
def circleSystem : ContinuousGeometricStepSystem (AddCircle (1 : ℝ)) Unit where
  src _ := 0
  tgt _ := 0
  realize _ := onceAround
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_const
end ComputationalHodge.LoopCharacters
namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
open ComputationalHodge.CircleHodge
open scoped NNReal Topology unitInterval
abbrev Trace (a b : CircleHodge.Circle) := GeometricTrace circleSystem.toGeometricStepSystem a b
def count {a b : CircleHodge.Circle} : Trace a b → ℤ
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => count p+count q
  | .symm p => -count p
def clamp (t : ℝ) : ℝ := max 0 (min 1 t)
/-- A finite piecewise-affine construction from the actual trace syntax.
Equality with the actual covering lift is proved separately. -/
noncomputable def rawLift {a b : CircleHodge.Circle} : Trace a b → ℝ → ℝ
  | .refl _ => fun _ => 0
  | .single _ => clamp
  | .trans p q => fun t => if t≤1/2 then rawLift p (2*t)
      else rawLift p 1+rawLift q (2*t-1)
  | .symm p => fun t => rawLift p (1-t)-rawLift p 1
theorem trace_endpoints {a b : CircleHodge.Circle} (p : Trace a b) : a=b := by induction p <;> aesop
theorem rawLift_zero {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 0=0 := by induction p <;> simp_all [rawLift,clamp]
theorem rawLift_one {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 1=(count p : ℝ) := by
  induction p with
  | refl _ => norm_num [rawLift,count]
  | single _ => norm_num [rawLift,clamp,count]
  | trans p q hp hq => norm_num [rawLift,count,hp,hq]
  | symm p hp => simp [rawLift,count,rawLift_zero,hp]
/-- Real-cut gluing; the nonoptimal sum bound keeps the contract elementary. -/
theorem cut_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0} {c : ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hc : f c=g c) : LipschitzWith (K+L) (fun x => if x≤c then f x else g x) := by
  have cross (x y : ℝ) (hx : x≤c) (hy : c≤y) :
      dist (f x) (g y)≤((K+L : ℝ≥0) : ℝ)*dist x y := by
    calc
      dist (f x) (g y)≤dist (f x) (f c)+dist (f c) (g y) := dist_triangle _ _ _
      _ = dist (f x) (f c)+dist (g c) (g y) := by rw [hc]
      _ ≤ (K : ℝ)*dist x c+(L : ℝ)*dist c y :=
        add_le_add (hf.dist_le_mul x c) (hg.dist_le_mul c y)
      _ ≤ ((K+L : ℝ≥0) : ℝ)*dist x y := by
        simp only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hx),
          abs_of_nonpos (sub_nonpos.mpr hy),
          abs_of_nonpos (sub_nonpos.mpr (hx.trans hy)),NNReal.coe_add]
        nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hy),
          mul_nonneg L.coe_nonneg (sub_nonneg.mpr hx)]
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  by_cases hx : x≤c <;> by_cases hy : y≤c
  · simpa only [ite_eq_left hx,ite_eq_left hy] using (hf.weaken (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0)≤L))).dist_le_mul x y
  · simpa only [ite_eq_left hx,ite_eq_right hy] using cross x y hx (not_le.mp hy).le
  · simpa only [ite_eq_right hx,ite_eq_left hy,dist_comm] using cross y x hy (not_le.mp hx).le
  · simpa only [ite_eq_right hx,ite_eq_right hy] using (hg.weaken (le_add_of_nonneg_left (bot_le : (0 : ℝ≥0)≤K))).dist_le_mul x y
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
theorem rawLift_one_coe {a b : CircleHodge.Circle} (p : Trace a b) : ((rawLift p 1 : ℝ) : CircleHodge.Circle)=0 := by
  rw [rawLift_one]
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
  exact ⟨count p,by simp⟩
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
/-- The actual covering lift of the actual path, extended by the interval projection. -/
noncomputable def actualLift (p : Trace 0 0) (t : ℝ) : ℝ :=
  circleLift (GeometricTrace.realize p) (Set.projIcc 0 1 zero_le_one t)
theorem rawLift_eq_cover (p : Trace 0 0) (t : unitInterval) : rawLift p (t : ℝ)=circleLift (GeometricTrace.realize p) t := by
  have h : (⟨fun t : unitInterval => rawLift p (t : ℝ),
      (rawLift_continuous p).comp continuous_subtype_val⟩ : C(unitInterval,ℝ))=
      circleLift (GeometricTrace.realize p) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    constructor
    · funext u
      simpa using rawLift_projects p u
    · exact rawLift_zero p
  exact congrArg (fun f : C(unitInterval,ℝ) => f t) h
theorem actualLift_eq_rawLift (p : Trace 0 0) : actualLift p=rawLift p := by
  funext t
  unfold actualLift
  rw [←rawLift_eq_cover p]
  exact rawLift_clamp p t
end ComputationalHodge.TraceIntegrals
namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
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
  | trans p q hp hq =>
    intro h
    rw [count,hp h,hq (fun hb => h ((trace_endpoints p).trans hb)),zero_add]
  | symm p hp =>
    intro h
    rw [count,hp (fun ha => h ((trace_endpoints p).symm.trans ha)),neg_zero]
theorem winding_realize_count (p : Trace 0 0) : winding (GeometricTrace.realize p)=(count p : ℝ) := by
  exact (rawLift_eq_cover p 1).symm.trans (rawLift_one p)
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
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- A real lift with regularity only on the interval, not a presumed period formula. -/
abbrev ACLift := {f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
  f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0}
def projectedLoop (L : ACLift) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((L.val (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    exact L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)
  source' := by simpa using congrArg (fun x : ℝ => (x : CircleHodge.Circle)) L.property.2.1
  target' := L.property.2.2
/-- Ordinary integration on this actual projected curve, against its real-lift derivative. -/
noncomputable def lineIntegral (α : Coefficient) (L : ACLift) : ℝ :=
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
theorem primitive_comp_ac (α : Coefficient) (L : ACLift) : AbsolutelyContinuousOnInterval (fun t => primitive α (L.val t)) 0 1 := by
  obtain ⟨K,hK⟩ := primitive_lipschitz α
  exact hK.comp_absolutelyContinuousOnInterval L.property.1
theorem chain_rule_ae (α : Coefficient) (L : ACLift) : ∀ᵐ t : ℝ, t∈uIcc (0 : ℝ) 1 → deriv (fun x => primitive α (L.val x)) t=cover α (L.val t)*deriv L.val t := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hmem
  exact ((primitive_hasDerivAt α (L.val t)).comp t (ht hmem).hasDerivAt).deriv
theorem lineIntegral_eq_cover (α : Coefficient) (L : ACLift) : lineIntegral α L=∫ t in (0 : ℝ)..1,cover α (L.val t)*deriv L.val t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have h : t∈Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  exact congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t) (Set.projIcc_of_mem zero_le_one h)
/-- The actual projected-curve integrand is interval integrable. -/
theorem line_integrand_integrable (α : Coefficient) (L : ACLift) : IntervalIntegrable (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t) volume 0 1 := by
  apply (primitive_comp_ac α L).intervalIntegrable_deriv.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (chain_rule_ae α L)] with t ht hd
  have h : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)
  have hp : (Set.projIcc 0 1 zero_le_one t : ℝ) = t := by rw [Set.projIcc_of_mem zero_le_one h]
  change deriv (fun x => primitive α (L.val x)) t = α ((L.val (Set.projIcc 0 1 zero_le_one t : ℝ) : ℝ) : CircleHodge.Circle) * deriv L.val t
  rw [hp]
  exact hd (uIoc_subset_uIcc ht)
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
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Every actual raw finite computational trace is admitted without smoothing it. -/
noncomputable def fromTrace (p : Trace 0 0) : ACLift :=
  ⟨actualLift p,by
    obtain ⟨K,hK⟩ := rawLift_lipschitz p
    rw [← actualLift_eq_rawLift] at hK
    exact hK.lipschitzOnWith.absolutelyContinuousOnInterval,
    by rw [actualLift_eq_rawLift,rawLift_zero],
    by rw [actualLift_eq_rawLift,rawLift_one];simp⟩
theorem projected_fromTrace (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := by
  ext t
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle)=GeometricTrace.realize p t
  have h := congrFun (circleCover.liftPath_lifts
    (GeometricTrace.realize p).toContinuousMap 0 (by simp)) t
  simpa [actualLift,circleLift,Set.projIcc_of_mem zero_le_one t.property] using h
theorem lineIntegral_fromTrace_harmonic (α : Coefficient) (p : Trace 0 0) : lineIntegral α (fromTrace p)=period p (meanHarmonic α) := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift p 1=period p (meanCochain α)
  rw [actualLift_eq_rawLift,rawLift_one,period_mean_count]
end ComputationalHodge.ACLifts
namespace ComputationalHodge.CircleHodge
open Set
/-- Exactness requires an actual circle potential and its actual C¹ derivative. -/
def ExactCoefficient (α : Coefficient) : Prop :=
  ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x
theorem mean_sub (α β : Coefficient) : mean (α-β)=mean α-mean β := by
  change (∫ x in (0 : ℝ)..1,cover α x-cover β x)=_
  exact intervalIntegral.integral_sub ((cover_continuous α).intervalIntegrable 0 1)
    ((cover_continuous β).intervalIntegrable 0 1)
theorem exact_mean_zero {α : Coefficient} (h : ExactCoefficient α) : mean α=0 := by
  obtain ⟨F,hF,hd⟩ := h
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc hF.contDiffOn (by norm_num : (0 : ℝ)≤1)
  have he : (∫ x in (0 : ℝ)..1,deriv (cover F) x)=mean α :=
    intervalIntegral.integral_congr (fun x _ => hd x)
  rw [he] at h
  have hp := cover_periodic F 0
  simp only [zero_add] at hp
  exact h.trans (sub_eq_zero.mpr hp)
end ComputationalHodge.CircleHodge
namespace ComputationalHodge.MetricHodge
open ComputationalHodge.CircleHodge MeasureTheory Set
/-- Positive continuous length density. The coordinate convention is ds=ρ dx. -/
abbrev Density := {ρ : Coefficient // ∀ q,0<ρ q}
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
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
/-- Positive C¹ length density, in the coordinate convention ds=ρ dx. -/
abbrev RegularDensity := {ρ : Density // ContDiff ℝ 1 (cover ρ.val)}
/-- Actual C² circle functions, not arbitrary real functions with totalized derivatives. -/
def C2Space : Submodule ℝ Coefficient where
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
/-- The actual continuous circle Laplacian δd, with the nonnegative geometer's sign. -/
noncomputable def laplacian (ρ : RegularDensity) (u : C2Coefficient) : Coefficient where
  toFun q := -(derivativeCoefficient (flux ρ u) (flux_c1 ρ u) q)/ρ.val.val q
  continuous_toFun := (derivativeCoefficient (flux ρ u) (flux_c1 ρ u)).continuous.neg.div
    ρ.val.val.continuous (density_ne ρ.val)
theorem laplacian_cover (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) : cover (laplacian ρ u) x=-(deriv (fun t => deriv (cover u.val) t/cover ρ.val.val t) x)/cover ρ.val.val x := rfl
noncomputable def weightedMean (ρ : RegularDensity) (f : Coefficient) : ℝ := mean (ρ.val.val*f)
theorem weightedMean_laplacian (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (laplacian ρ u)=0 := by
  apply exact_mean_zero
  refine ⟨-flux ρ u,(flux_c1 ρ u).neg,fun x => ?_⟩
  have hd:=(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.neg).deriv
  change deriv (-cover (flux ρ u)) x=_
  rw [hd]
  change _=cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)
  field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]
theorem green_identity (ρ : RegularDensity) (u v : C2Coefficient) : (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)= ∫ x in (0 : ℝ)..1,cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x := by
  have hi:=((flux_c1 ρ u).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1)).integral_mul_deriv_eq_deriv_mul
    ((c2_c1 v).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1))
  have hp:=cover_periodic (flux ρ u) 0
  have hq:=cover_periodic v.val 0
  simp only [zero_add] at hp hq
  rw [hp,hq,sub_self,zero_sub] at hi
  have hl : (fun x => cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      fun x => -(deriv (cover (flux ρ u)) x*cover v.val x) := by
    funext x
    change cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)*cover v.val x=_
    field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]
  have hr : (fun x => cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x)=
      fun x => cover (flux ρ u) x*deriv (cover v.val) x := by
    funext x
    change deriv (cover u.val) x*deriv (cover v.val) x/cover ρ.val.val x=
      (deriv (cover u.val) x/cover ρ.val.val x)*deriv (cover v.val) x
    ring
  rw [hl,hr,intervalIntegral.integral_neg]
  exact hi.symm
theorem pairing_symmetry (ρ : RegularDensity) (u v : C2Coefficient) : (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)= ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover u.val x*cover (laplacian ρ v) x := by
  rw [green_identity]
  calc
    _ = ∫ x in (0 : ℝ)..1,cover (gradient v) x*cover (gradient u) x/cover ρ.val.val x :=
      intervalIntegral.integral_congr (fun _ _ => by ring)
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ v) x*cover u.val x := (green_identity ρ v u).symm
    _ = _ := intervalIntegral.integral_congr (fun _ _ => by ring)
noncomputable def cosine : Coefficient where
  toFun q := (AddCircle.toCircle q : ℂ).re
  continuous_toFun := by fun_prop
theorem cosine_cover (x : ℝ) : cover cosine x=Real.cos (2*Real.pi*x) := by
  change (AddCircle.toCircle (x : CircleHodge.Circle) : ℂ).re=_
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  norm_num [Complex.exp_re]
end ComputationalHodge.Poisson
namespace ComputationalHodge.GreenOperator
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open MeasureTheory Set
theorem weightedMean_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) : weightedMean ρ (c•f)=c*weightedMean ρ f := by
  have h : ρ.val.val*(c•f)=c•(ρ.val.val*f) := by ext q;change _*(c*_) = c*(_*_);ring
  rw [weightedMean,h,mean_smul]
  rfl
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/
noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
end ComputationalHodge.GreenOperator
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator
/-- Actual normalized twice continuously differentiable circle functions; no Banach claim. -/
abbrev Domain (ρ : RegularDensity) := {u : C2Coefficient // weightedMean ρ u.val=0}
end ComputationalHodge.CircleFredholm
namespace ComputationalHodge.ResonanceObstruction
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
theorem pairing_comm (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=pairing ρ g f := by
  unfold pairing
  congr 1
  ext q
  change ρ.val.val q*f q*g q=ρ.val.val q*g q*f q
  ring
theorem pairing_sub_left (ρ : RegularDensity) (f g h : Coefficient) : pairing ρ (f-g) h=pairing ρ f h-pairing ρ g h := by
  have he : ρ.val.val*(f-g)*h=ρ.val.val*f*h-ρ.val.val*g*h := by
    ext q
    change ρ.val.val q*(f q-g q)*h q=ρ.val.val q*f q*h q-ρ.val.val q*g q*h q
    ring
  rw [pairing,he,mean_sub]
  rfl
theorem pairing_smul_left (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) : pairing ρ (c•f) g=c*pairing ρ f g := by
  have he : ρ.val.val*(c•f)*g=c•(ρ.val.val*f*g) := by
    ext q
    change ρ.val.val q*(c*f q)*g q=c*(ρ.val.val q*f q*g q)
    ring
  rw [pairing,he,mean_smul]
  rfl
theorem pairing_smul_right (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) : pairing ρ f (c•g)=c*pairing ρ f g := by
  rw [pairing_comm,pairing_smul_left,pairing_comm ρ g f]
theorem pairing_positive (ρ : RegularDensity) (f : Coefficient) (hf : f≠0) : 0<pairing ρ f f := by
  obtain ⟨q,hq⟩ : ∃ q,f q≠0 := by
    by_contra h
    apply hf
    ext q
    exact not_ne_iff.mp (not_exists.mp h q)
  rw [pairing,mean_circle]
  apply integral_pos_of_integrable_nonneg_nonzero (ρ.val.val*f*f).continuous
    (continuous_integrable (ρ.val.val*f*f).continuous)
    (fun q => by
      change 0≤ρ.val.val q*f q*f q
      simpa only [mul_assoc] using mul_nonneg (ρ.val.property q).le (mul_self_nonneg (f q)))
  change ρ.val.val q*f q*f q≠0
  exact mul_ne_zero (mul_ne_zero (density_ne ρ.val q) hq) hq
theorem laplacian_symmetric (ρ : RegularDensity) (u v : C2Coefficient) : pairing ρ (laplacian ρ u) v.val=pairing ρ u.val (laplacian ρ v) :=
  pairing_symmetry ρ u v
/-- Necessary orthogonality for actual shifted solutions; all C2 competitors are covered. -/
theorem forcing_orthogonal (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (f : Coefficient) (hv : laplacian ρ v=μ•v.val) (hu : laplacian ρ u-μ•u.val=f) : pairing ρ f v.val=0 := by
  rw [← hu,pairing_sub_left,laplacian_symmetric,hv,pairing_smul_right,pairing_smul_left,sub_self]
theorem mode_obstructed (ρ : RegularDensity) (μ : ℝ) (v : C2Coefficient) (hn : v.val≠0) (hv : laplacian ρ v=μ•v.val) : ¬∃ u : C2Coefficient,laplacian ρ u-μ•u.val=v.val := by
  rintro ⟨u,hu⟩
  exact (ne_of_gt (pairing_positive ρ v.val hn)) (forcing_orthogonal ρ μ u v v.val hv hu)
theorem mode_periods (ρ : RegularDensity) (v : Domain ρ) : (∀ p : Trace 0 0,lineIntegral (ρ.val.val*v.val.val) (fromTrace p)=0) ∧ (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*v.val.val)).val=0) := by
  have h (p : Trace 0 0) : lineIntegral (ρ.val.val*v.val.val) (fromTrace p)=0 := by
    rw [lineIntegral_eq_mean,show mean (ρ.val.val*v.val.val)=0 from v.property,zero_mul]
  exact ⟨h,fun p => (lineIntegral_fromTrace_harmonic _ p).symm.trans (h p)⟩
/-- The constant unit density on the scalar circle. -/
noncomputable def flatDensity : RegularDensity :=
  ⟨⟨constant 1,fun _ => by change 0<(1 : ℝ);norm_num⟩,by
    change ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))
    exact contDiff_const⟩
end ComputationalHodge.ResonanceObstruction
namespace ComputationalHodge.Arclength
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval
noncomputable def coordinate (ρ : Density) (x : ℝ) : ℝ := primitive ρ.val x/mean ρ.val
theorem coordinate_hasDerivAt (ρ : Density) (x : ℝ) : HasDerivAt (coordinate ρ) (cover ρ.val x/mean ρ.val) x :=
  (primitive_hasDerivAt ρ.val x).div_const _
theorem coordinate_zero (ρ : Density) : coordinate ρ 0=0 := by simp [coordinate,primitive]
theorem coordinate_shift (ρ : Density) (x : ℝ) (n : ℤ) : coordinate ρ (x+n)=coordinate ρ x+n := by
  have h := (cover_periodic ρ.val).intervalIntegral_add_zsmul_eq n x
    (fun a b => (cover_continuous ρ.val).intervalIntegrable a b)
  rw [(cover_periodic ρ.val).intervalIntegral_add_eq x 0] at h
  simp only [zero_add,zsmul_eq_mul,mul_one] at h
  have ha := intervalIntegral.integral_add_adjacent_intervals
    ((cover_continuous ρ.val).intervalIntegrable (μ:=volume) 0 x)
    ((cover_continuous ρ.val).intervalIntegrable (μ:=volume) x (x+n))
  unfold coordinate primitive
  rw [← ha,h]
  change ((∫ t in (0 : ℝ)..x,cover ρ.val t)+(n : ℝ)*mean ρ.val)/mean ρ.val=_
  field_simp [ne_of_gt (mean_pos ρ)]
theorem coordinate_int (ρ : Density) (n : ℤ) : coordinate ρ (n : ℝ)=n := by
  simpa [coordinate_zero] using coordinate_shift ρ 0 n
theorem coordinate_strictMono (ρ : Density) : StrictMono (coordinate ρ) :=
  strictMono_of_hasDerivAt_pos (coordinate_hasDerivAt ρ)
    (fun _ => div_pos (ρ.property _) (mean_pos ρ))
theorem coordinate_surjective (ρ : Density) : Function.Surjective (coordinate ρ) := by
  intro y
  have hc : Continuous (coordinate ρ) := continuous_iff_continuousAt.mpr (fun x => (coordinate_hasDerivAt ρ x).continuousAt)
  have ha : ((⌊y⌋ : ℤ) : ℝ)≤((⌊y⌋+1 : ℤ) : ℝ) := by norm_num
  have hy : y∈Icc (coordinate ρ (⌊y⌋ : ℤ)) (coordinate ρ ((⌊y⌋+1 : ℤ) : ℝ)) := by
    rw [coordinate_int,coordinate_int]
    exact ⟨Int.floor_le y,by exact_mod_cast (Int.lt_floor_add_one y).le⟩
  obtain ⟨x,_,hx⟩:=intermediate_value_Icc ha hc.continuousOn hy
  exact ⟨x,hx⟩
noncomputable def coordinateHomeomorph (ρ : Density) : ℝ ≃ₜ ℝ :=
  ((coordinate_strictMono ρ).orderIsoOfSurjective (coordinate ρ) (coordinate_surjective ρ)).toHomeomorph
noncomputable def inverse (ρ : Density) : ℝ→ℝ := (coordinateHomeomorph ρ).symm
theorem coordinate_inverse (ρ : Density) (x : ℝ) : coordinate ρ (inverse ρ x)=x :=
  (coordinateHomeomorph ρ).apply_symm_apply x
theorem inverse_coordinate (ρ : Density) (x : ℝ) : inverse ρ (coordinate ρ x)=x :=
  (coordinateHomeomorph ρ).symm_apply_apply x
end ComputationalHodge.Arclength
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open scoped ContDiff
/-- The existing arclength coordinate has the regularity required for C² pullback. -/
theorem coordinate_contDiff_two (ρ : RegularDensity) : ContDiff ℝ 2 (coordinate ρ.val) := by
  have hd : deriv (coordinate ρ.val) =
      fun x => cover ρ.val.val x / mean ρ.val.val :=
    funext fun x => (coordinate_hasDerivAt ρ.val x).deriv
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) (coordinate ρ.val)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (coordinate_hasDerivAt ρ.val x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [hd]
    exact ρ.property.div_const _
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.ResonanceObstruction
open scoped ContDiff
theorem coordinate_cover_periodic (ρ : RegularDensity) (u : Coefficient) : Function.Periodic (fun x => cover u (coordinate ρ.val x)) 1 := by
  intro x
  have h : coordinate ρ.val (x + 1) = coordinate ρ.val x + 1 := by
    simpa using coordinate_shift ρ.val x 1
  change cover u (coordinate ρ.val (x + 1)) = cover u (coordinate ρ.val x)
  rw [h]
  exact cover_periodic u _
/-- Pullback along the actual normalized arclength coordinate. -/
noncomputable def pullback (ρ : RegularDensity) (u : Coefficient) : Coefficient where
  toFun := (coordinate_cover_periodic ρ u).lift
  continuous_toFun := ((cover_continuous u).comp (coordinate_contDiff_two ρ).continuous).quotient_liftOn' _
theorem cover_pullback (ρ : RegularDensity) (u : Coefficient) (x : ℝ) : cover (pullback ρ u) x = cover u (coordinate ρ.val x) := rfl
noncomputable def pullbackC2 (ρ : RegularDensity) (u : C2Coefficient) : C2Coefficient :=
  ⟨pullback ρ u.val, by
    change ContDiff ℝ 2 (fun x => cover u.val (coordinate ρ.val x))
    exact (show ContDiff ℝ 2 (cover u.val) from u.property).comp (coordinate_contDiff_two ρ)⟩
/-- Conjugacy for the actual positive weighted circle Laplacian on every C² coefficient. -/
theorem laplacian_pullback (ρ : RegularDensity) (u : C2Coefficient) : laplacian ρ (pullbackC2 ρ u) = (mean ρ.val.val)⁻¹ ^ 2 • pullback ρ (laplacian flatDensity u) := by
  have hm : mean ρ.val.val ≠ 0 := ne_of_gt (mean_pos ρ.val)
  have hp : ∀ x, cover ρ.val.val x ≠ 0 := fun x => density_ne ρ.val (x : CircleHodge.Circle)
  have hd : deriv (cover (pullbackC2 ρ u).val) =
      fun t => deriv (cover u.val) (coordinate ρ.val t) * (cover ρ.val.val t / mean ρ.val.val) := by
    funext t
    exact (((contDiff_one_iff_deriv.mp (c2_c1 u)).1 (coordinate ρ.val t)).hasDerivAt.comp t
      (coordinate_hasDerivAt ρ.val t)).deriv
  have hf : (fun t => deriv (cover (pullbackC2 ρ u).val) t / cover ρ.val.val t) =
      fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val := by
    funext t
    rw [hd]
    field_simp [hm, hp t]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian ρ (pullbackC2 ρ u)) x =
    (mean ρ.val.val)⁻¹ ^ 2 * cover (pullback ρ (laplacian flatDensity u)) x
  rw [laplacian_cover, cover_pullback, laplacian_cover, hf]
  change -(deriv (fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val) x) /
      cover ρ.val.val x = (mean ρ.val.val)⁻¹ ^ 2 *
        (-(deriv (fun t => deriv (cover u.val) t / (1 : ℝ)) (coordinate ρ.val x)) / 1)
  simp only [div_one]
  have h := ((((contDiff_one_iff_deriv.mp (c2_deriv_c1 u)).1 (coordinate ρ.val x)).hasDerivAt.comp x
    (coordinate_hasDerivAt ρ.val x)).div_const (mean ρ.val.val)).deriv
  change deriv (fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val) x = _ at h
  rw [h]
  field_simp [hm, hp x]
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.Arclength
open ComputationalHodge.Poisson
open ComputationalHodge.LoopCharacters
open scoped unitInterval
/-- The phase of the actual covering lift of the realized computational trace. -/
noncomputable def tracePhase (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : ℝ) : ℝ :=
  (n : ℝ) * coordinate ρ.val (actualLift p t)
theorem tracePhase_zero (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) : tracePhase ρ n p 0 = 0 := by
  simp [tracePhase, actualLift_eq_rawLift, rawLift_zero, coordinate_zero]
theorem tracePhase_one (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) : tracePhase ρ n p 1 = (n : ℝ) * (count p : ℝ) := by
  simp [tracePhase, actualLift_eq_rawLift, rawLift_one, coordinate_int]
theorem tracePhase_continuous (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) : Continuous (tracePhase ρ n p) := by
  unfold tracePhase
  rw [actualLift_eq_rawLift]
  exact continuous_const.mul ((coordinate_contDiff_two ρ).continuous.comp (rawLift_continuous p))
/-- The actual mapped loop determined by the phase of the computational trace. -/
noncomputable def phaseLoop (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((tracePhase ρ n p (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((tracePhase_continuous ρ n p).comp continuous_subtype_val)
  source' := by simp [tracePhase_zero]
  target' := by
    change ((tracePhase ρ n p 1 : ℝ) : CircleHodge.Circle) = 0
    rw [tracePhase_one]
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
    exact ⟨(n : ℤ) * count p, by simp [zsmul_eq_mul]⟩
/-- The covering-map winding is the actual trace count multiplied by n. -/
theorem phaseLoop_winding (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) : winding (phaseLoop ρ n p) = (n : ℝ) * (count p : ℝ) := by
  have h : (⟨fun t : unitInterval => tracePhase ρ n p (t : ℝ),
      (tracePhase_continuous ρ n p).comp continuous_subtype_val⟩ : C(unitInterval, ℝ)) =
      circleLift (phaseLoop ρ n p) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      rfl
    · exact tracePhase_zero ρ n p
  unfold winding
  rw [← h]
  exact tracePhase_one ρ n p
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.ResonanceObstruction
noncomputable def cosineN (n : ℕ) : Coefficient where
  toFun q := cosine (n • q)
  continuous_toFun := by fun_prop
noncomputable def sineN (n : ℕ) : Coefficient where
  toFun q := (AddCircle.toCircle (n • q) : ℂ).im
  continuous_toFun := by fun_prop
theorem cosineN_cover (n : ℕ) (x : ℝ) : cover (cosineN n) x = Real.cos (2 * Real.pi * ((n : ℝ) * x)) := by
  change cosine (n • (x : CircleHodge.Circle)) = _
  rw [← AddCircle.coe_nsmul]
  change cover cosine (n • x) = _
  rw [cosine_cover]
  simp only [nsmul_eq_mul]
theorem sineN_cover (n : ℕ) (x : ℝ) : cover (sineN n) x = Real.sin (2 * Real.pi * ((n : ℝ) * x)) := by
  change (AddCircle.toCircle (n • (x : CircleHodge.Circle)) : ℂ).im = _
  rw [← AddCircle.coe_nsmul]
  simp only [nsmul_eq_mul]
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  norm_num [Complex.exp_im]
noncomputable def cosineNC2 (n : ℕ) : C2Coefficient := ⟨cosineN n, by
  have h : cover (cosineN n) = fun x => Real.cos (2 * Real.pi * ((n : ℝ) * x)) := funext (cosineN_cover n)
  change ContDiff ℝ 2 (cover (cosineN n))
  rw [h]
  fun_prop⟩
noncomputable def sineNC2 (n : ℕ) : C2Coefficient := ⟨sineN n, by
  have h : cover (sineN n) = fun x => Real.sin (2 * Real.pi * ((n : ℝ) * x)) := funext (sineN_cover n)
  change ContDiff ℝ 2 (cover (sineN n))
  rw [h]
  fun_prop⟩
noncomputable def angular (n : ℕ) : ℝ := 2 * Real.pi * n
noncomputable def frequencyN (n : ℕ) : ℝ := angular n ^ 2
theorem cosineN_eigen (n : ℕ) : laplacian flatDensity (cosineNC2 n) = frequencyN n • cosineN n := by
  have he : cover (cosineN n) = fun x => Real.cos (angular n * x) := by
    funext x
    rw [cosineN_cover]
    congr 1
    unfold angular
    ring
  have h1 (x : ℝ) : HasDerivAt (cover (cosineN n)) (-(angular n) * Real.sin (angular n * x)) x := by
    rw [he]
    have h := (((hasDerivAt_id x).const_mul (angular n)).cos)
    simp only [id_eq, mul_one] at h
    convert h using 1; ring
  have h2 (x : ℝ) : HasDerivAt (fun t => -(angular n) * Real.sin (angular n * t))
      (-frequencyN n * Real.cos (angular n * x)) x := by
    have h := ((((hasDerivAt_id x).const_mul (angular n)).sin).const_mul (-(angular n)))
    simp only [id_eq, mul_one] at h
    convert h using 1; simp only [frequencyN]; ring
  have hd : deriv (cover (cosineN n)) = fun t => -(angular n) * Real.sin (angular n * t) :=
    funext fun x => (h1 x).deriv
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian flatDensity (cosineNC2 n)) x = frequencyN n * cover (cosineN n) x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv (cover (cosineN n)) t / (1 : ℝ)) x) / 1 = _
  simp only [div_one]
  rw [hd, (h2 x).deriv, he]
  ring
theorem sineN_eigen (n : ℕ) : laplacian flatDensity (sineNC2 n) = frequencyN n • sineN n := by
  have he : cover (sineN n) = fun x => Real.sin (angular n * x) := by
    funext x
    rw [sineN_cover]
    congr 1
    unfold angular
    ring
  have h1 (x : ℝ) : HasDerivAt (cover (sineN n)) (angular n * Real.cos (angular n * x)) x := by
    rw [he]
    have h := (((hasDerivAt_id x).const_mul (angular n)).sin)
    simp only [id_eq, mul_one] at h
    convert h using 1; ring
  have h2 (x : ℝ) : HasDerivAt (fun t => angular n * Real.cos (angular n * t))
      (-frequencyN n * Real.sin (angular n * x)) x := by
    have h := ((((hasDerivAt_id x).const_mul (angular n)).cos).const_mul (angular n))
    simp only [id_eq, mul_one] at h
    convert h using 1; simp only [frequencyN]; ring
  have hd : deriv (cover (sineN n)) = fun t => angular n * Real.cos (angular n * t) :=
    funext fun x => (h1 x).deriv
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian flatDensity (sineNC2 n)) x = frequencyN n * cover (sineN n) x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv (cover (sineN n)) t / (1 : ℝ)) x) / 1 = _
  simp only [div_one]
  rw [hd, (h2 x).deriv, he]
  ring
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters
noncomputable def curvedFrequency (ρ : RegularDensity) (n : ℕ) : ℝ :=
  (mean ρ.val.val)⁻¹ ^ 2 * frequencyN n
noncomputable def curvedCosine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (cosineNC2 n)
noncomputable def curvedSine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (sineNC2 n)
theorem curvedFrequency_positive (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : 0 < curvedFrequency ρ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < mean ρ.val.val := mean_pos ρ.val
  unfold curvedFrequency frequencyN angular
  positivity
theorem transfer_eigen (ρ : RegularDensity) (u : C2Coefficient) (μ : ℝ) (hu : laplacian flatDensity u = μ • u.val) : laplacian ρ (pullbackC2 ρ u) = ((mean ρ.val.val)⁻¹ ^ 2 * μ) • (pullbackC2 ρ u).val := by
  rw [laplacian_pullback, hu]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change (mean ρ.val.val)⁻¹ ^ 2 * cover (pullback ρ (μ • u.val)) x =
    ((mean ρ.val.val)⁻¹ ^ 2 * μ) * cover (pullback ρ u.val) x
  rw [cover_pullback, cover_pullback]
  change (mean ρ.val.val)⁻¹ ^ 2 * (μ * cover u.val (coordinate ρ.val x)) = _
  ring
theorem curvedCosine_eigen (ρ : RegularDensity) (n : ℕ) : laplacian ρ (curvedCosine ρ n) = curvedFrequency ρ n • (curvedCosine ρ n).val :=
  transfer_eigen ρ (cosineNC2 n) (frequencyN n) (cosineN_eigen n)
theorem curvedSine_eigen (ρ : RegularDensity) (n : ℕ) : laplacian ρ (curvedSine ρ n) = curvedFrequency ρ n • (curvedSine ρ n).val :=
  transfer_eigen ρ (sineNC2 n) (frequencyN n) (sineN_eigen n)
theorem curvedCosine_zero (ρ : RegularDensity) (n : ℕ) : (curvedCosine ρ n).val 0 = 1 := by
  change cover (pullback ρ (cosineN n)) 0 = 1
  rw [cover_pullback, coordinate_zero, cosineN_cover]
  simp
theorem curvedSine_zero (ρ : RegularDensity) (n : ℕ) : (curvedSine ρ n).val 0 = 0 := by
  change cover (pullback ρ (sineN n)) 0 = 0
  rw [cover_pullback, coordinate_zero, sineN_cover]
  simp
theorem curvedSine_quarter (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : (curvedSine ρ n).val ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle) = 1 := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  change cover (pullback ρ (sineN n)) (inverse ρ.val (1 / (4 * (n : ℝ)))) = 1
  rw [cover_pullback, coordinate_inverse, sineN_cover]
  have h : 2 * Real.pi * ((n : ℝ) * (1 / (4 * (n : ℝ)))) = Real.pi / 2 := by
    field_simp [hne]; ring
  rw [h, Real.sin_pi_div_two]
theorem curvedModes_independent (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) (a b : ℝ) (h : a • (curvedCosine ρ n).val + b • (curvedSine ρ n).val = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (fun f : Coefficient => f 0) h
  change a * (curvedCosine ρ n).val 0 + b * (curvedSine ρ n).val 0 = 0 at h0
  rw [curvedCosine_zero, curvedSine_zero] at h0
  have ha : a = 0 := by linarith
  have h1 := congrArg (fun f : Coefficient => f ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle)) h
  change a * (curvedCosine ρ n).val _ + b * (curvedSine ρ n).val _ = 0 at h1
  rw [ha, curvedSine_quarter ρ hn] at h1
  exact ⟨ha, by linarith⟩
theorem curvedCosine_nonzero (ρ : RegularDensity) (n : ℕ) : (curvedCosine ρ n).val ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Coefficient => f 0) h
  rw [curvedCosine_zero] at h0
  norm_num at h0
theorem curvedSine_nonzero (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : (curvedSine ρ n).val ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : Coefficient => f ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle)) h
  rw [curvedSine_quarter ρ hn] at h1
  norm_num at h1
theorem eigen_mean_zero (ρ : RegularDensity) (u : C2Coefficient) (μ : ℝ) (hμ : μ ≠ 0) (hu : laplacian ρ u = μ • u.val) : weightedMean ρ u.val = 0 := by
  have h := weightedMean_laplacian ρ u
  rw [hu, weightedMean_smul] at h
  exact (mul_eq_zero.mp h).resolve_left hμ
theorem curvedCosine_obstruction (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : (∀ p : Trace 0 0, lineIntegral (ρ.val.val * (curvedCosine ρ n).val) (fromTrace p) = 0) ∧ (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * (curvedCosine ρ n).val)).val = 0) ∧ ¬ ∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = (curvedCosine ρ n).val := by
  let v : Domain ρ := ⟨curvedCosine ρ n, eigen_mean_zero ρ _ _
    (ne_of_gt (curvedFrequency_positive ρ hn)) (curvedCosine_eigen ρ n)⟩
  exact ⟨(mode_periods ρ v).1, (mode_periods ρ v).2,
    mode_obstructed ρ _ _ (curvedCosine_nonzero ρ n) (curvedCosine_eigen ρ n)⟩
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open scoped unitInterval
/-- The geometric cosine on the actual realized trace is the cosine of its lifted phase. -/
theorem curvedCosine_on_trace (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : unitInterval) : (curvedCosine ρ n).val (GeometricTrace.realize p t) = Real.cos (2 * Real.pi * tracePhase ρ n p (t : ℝ)) := by
  have hp := congrArg (fun q : _root_.Path (0 : CircleHodge.Circle) 0 => q t) (projected_fromTrace p)
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle) = GeometricTrace.realize p t at hp
  rw [← hp]
  change cover (pullback ρ (cosineN n)) (actualLift p t) = _
  rw [cover_pullback, cosineN_cover]
  rfl
/-- The same statement for the independent sine mode. -/
theorem curvedSine_on_trace (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : unitInterval) : (curvedSine ρ n).val (GeometricTrace.realize p t) = Real.sin (2 * Real.pi * tracePhase ρ n p (t : ℝ)) := by
  have hp := congrArg (fun q : _root_.Path (0 : CircleHodge.Circle) 0 => q t) (projected_fromTrace p)
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle) = GeometricTrace.realize p t at hp
  rw [← hp]
  change cover (pullback ρ (sineN n)) (actualLift p t) = _
  rw [cover_pullback, sineN_cover]
  rfl
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.Arclength
/-- The constructed resonant shifts strictly increase with the natural frequency. -/
theorem curvedFrequency_strictMono (ρ : RegularDensity) : StrictMono (curvedFrequency ρ) := by
  intro m n hmn
  have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hm : 0 ≤ angular m := by unfold angular; positivity
  have hn : 0 ≤ angular n := by unfold angular; positivity
  unfold curvedFrequency frequencyN
  apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos (inv_pos.mpr (mean_pos ρ.val)))
  exact (sq_lt_sq₀ hm hn).2 (mul_lt_mul_of_pos_left hmn' (by positivity : 0 < 2 * Real.pi))
/-- The independent sine mode is also period-compatible and obstructs the shifted equation. -/
theorem curvedSine_obstruction (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : (∀ p : Trace 0 0, lineIntegral (ρ.val.val * (curvedSine ρ n).val) (fromTrace p) = 0) ∧ (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * (curvedSine ρ n).val)).val = 0) ∧ ¬ ∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = (curvedSine ρ n).val := by
  let v : Domain ρ := ⟨curvedSine ρ n, eigen_mean_zero ρ _ _
    (ne_of_gt (curvedFrequency_positive ρ hn)) (curvedSine_eigen ρ n)⟩
  exact ⟨(mode_periods ρ v).1, (mode_periods ρ v).2,
    mode_obstructed ρ _ _ (curvedSine_nonzero ρ hn) (curvedSine_eigen ρ n)⟩
end ComputationalHodge.ArclengthSpectrum
