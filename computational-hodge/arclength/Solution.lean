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
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
/-! Proof-complete shared generated source. All retained declarations and proofs
are retained from the ordered modular sources. Signature whitespace is reflowed; complete proof bodies remain unchanged.
The upstream MIT attribution and SOURCE-LICENSE.txt remain applicable. -/
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
theorem trace_endpoints {a b : CircleHodge.Circle} (p : Trace a b) : a=b := by
  induction p with
  | refl _ => rfl
  | single _ => rfl
  | trans p q hp hq => exact hp.trans hq
  | symm p hp => exact hp.symm
theorem rawLift_zero {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 0=0 := by
  induction p with
  | refl _ => rfl
  | single _ => norm_num [rawLift,clamp]
  | trans p q hp hq => norm_num [rawLift,hp]
  | symm p hp => simp [rawLift]
theorem rawLift_one {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 1=(count p : ℝ) := by
  induction p with
  | refl _ => norm_num [rawLift,count]
  | single _ => norm_num [rawLift,clamp,count]
  | trans p q hp hq => norm_num [rawLift,count,hp,hq]
  | symm p hp => simp [rawLift,count,rawLift_zero,hp]
theorem rawLift_continuous {a b : CircleHodge.Circle} (p : Trace a b) : Continuous (rawLift p) := by
  induction p with
  | refl _ => exact continuous_const
  | single _ => unfold rawLift clamp; fun_prop
  | trans p q hp hq =>
    apply Continuous.if_le
      (hp.comp (continuous_const.mul continuous_id))
      (continuous_const.add (hq.comp ((continuous_const.mul continuous_id).sub continuous_const)))
      continuous_id continuous_const
    intro x hx
    change x=(1 : ℝ)/2 at hx
    subst x
    norm_num [rawLift_zero]
  | symm p hp => exact (hp.comp (continuous_const.sub continuous_id)).sub continuous_const
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
  · simp only [ite_eq_left hx,ite_eq_left hy]
    exact (hf.dist_le_mul x y).trans (by
      simp only [NNReal.coe_add];nlinarith [mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))])
  · simpa only [ite_eq_left hx,ite_eq_right hy] using cross x y hx (not_le.mp hy).le
  · simpa only [ite_eq_right hx,ite_eq_left hy,dist_comm] using cross y x hy (not_le.mp hx).le
  · simp only [ite_eq_right hx,ite_eq_right hy]
    exact (hg.dist_le_mul x y).trans (by
      simp only [NNReal.coe_add];nlinarith [mul_nonneg K.coe_nonneg (dist_nonneg (x := x) (y := y))])
theorem affine_lipschitz (a b : ℝ) : LipschitzWith ‖a‖₊ (fun x : ℝ => a*x+b) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  change |(a*x+b)-(a*y+b)| ≤ |a| * |x-y|
  have h : (a*x+b)-(a*y+b)=a*(x-y) := by ring
  rw [h,abs_mul]
theorem shift_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) : LipschitzWith K (fun x => c+f x) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub] using hf.dist_le_mul x y
theorem rawLift_lipschitz {a b : CircleHodge.Circle} (p : Trace a b) : ∃ K : ℝ≥0,LipschitzWith K (rawLift p) := by
  induction p with
  | refl _ => exact ⟨0,LipschitzWith.const 0⟩
  | single _ => exact ⟨1,(LipschitzWith.id.const_min 1).const_max 0⟩
  | trans p q hp hq =>
    obtain ⟨K,hK⟩ := hp
    obtain ⟨L,hL⟩ := hq
    have hl : LipschitzWith (K*‖(2 : ℝ)‖₊) (fun x => rawLift p (2*x)) := by
      simpa only [Function.comp_def,add_zero] using hK.comp (affine_lipschitz 2 0)
    have hr : LipschitzWith (L*‖(2 : ℝ)‖₊) (fun x => rawLift q (2*x-1)) := by
      simpa only [Function.comp_def,sub_eq_add_neg] using hL.comp (affine_lipschitz 2 (-1))
    refine ⟨K*‖(2 : ℝ)‖₊+L*‖(2 : ℝ)‖₊,?_⟩
    exact cut_lipschitz hl (shift_lipschitz hr (rawLift p 1)) (by norm_num [rawLift_zero])
  | symm p hp =>
    obtain ⟨K,hK⟩ := hp
    have h : LipschitzWith (K*‖(-1 : ℝ)‖₊) (fun x => rawLift p (1-x)) := by
      convert hK.comp (affine_lipschitz (-1) 1) using 1
      funext x
      congr 1
      ring
    refine ⟨K*‖(-1 : ℝ)‖₊,?_⟩
    change LipschitzWith (K*‖(-1 : ℝ)‖₊) (fun x => rawLift p (1-x)-rawLift p 1)
    simpa only [sub_eq_add_neg,add_comm] using shift_lipschitz h (-rawLift p 1)
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
    by_cases h : (t : ℝ)≤1/2
    · rw [dite_eq_left h]
      change ((if (t : ℝ)≤1/2 then rawLift p (2*t) else rawLift p 1+rawLift q (2*t-1) : ℝ) : CircleHodge.Circle)+_= _
      rw [ite_eq_left h]
      exact hp ⟨2*t,⟨by linarith [t.2.1],by linarith⟩⟩
    · rw [dite_eq_right h]
      change ((if (t : ℝ)≤1/2 then rawLift p (2*t) else rawLift p 1+rawLift q (2*t-1) : ℝ) : CircleHodge.Circle)+_= _
      rw [ite_eq_right h,AddCircle.coe_add,rawLift_one_coe,zero_add]
      conv_lhs => rhs; rw [trace_endpoints p]
      exact hq ⟨2*t-1,⟨by linarith [not_le.mp h],by linarith [t.2.2]⟩⟩
  | symm p hp =>
    change ((rawLift p (1-(t : ℝ))-rawLift p 1 : ℝ) : CircleHodge.Circle)+_=
      GeometricTrace.realize p (σ t)
    rw [AddCircle.coe_sub,rawLift_one_coe,sub_zero]
    conv_lhs => rhs; rw [←trace_endpoints p]
    exact hp (σ t)
theorem rawLift_outside {a b : CircleHodge.Circle} (p : Trace a b) : ∀ t : ℝ,(t≤0 → rawLift p t=0) ∧ (1≤t → rawLift p t=rawLift p 1) := by
  induction p with
  | refl _ => exact fun _ => ⟨fun _ => rfl,fun _ => rfl⟩
  | single _ =>
    intro t
    constructor
    · intro h; simp [rawLift,clamp,min_eq_right (h.trans zero_le_one),max_eq_left h]
    · intro h; simp [rawLift,clamp,min_eq_left h]
  | trans p q hp hq =>
    intro t
    constructor
    · intro ht
      have h : t≤1/2 := by linarith
      simp only [rawLift,ite_eq_left h]
      exact (hp (2*t)).1 (by linarith)
    · intro ht
      have h : ¬t≤1/2 := by linarith
      simp only [rawLift,ite_eq_right h]
      rw [(hq (2*t-1)).2 (by linarith)]
      norm_num
  | symm p hp =>
    intro t
    constructor
    · intro ht
      change rawLift p (1-t)-rawLift p 1=0
      rw [(hp (1-t)).2 (by linarith),sub_self]
    · intro ht
      change rawLift p (1-t)-rawLift p 1=rawLift p (1-1)-rawLift p 1
      rw [(hp (1-t)).1 (by linarith)]
      norm_num [rawLift_zero]
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
def unitCochain : Cochain Unit := WithLp.toLp 2 (fun _ => 1)
def unitTrace : Trace 0 0 := .single ()
noncomputable def meanCochain (α : Coefficient) : Cochain Unit := WithLp.toLp 2 (fun _ => mean α)
theorem period_mean_count (α : Coefficient) {a b : CircleHodge.Circle} (p : Trace a b) : period p (meanCochain α)=mean α*(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change mean α=mean α*((1 : ℤ) : ℝ);rw [Int.cast_one,mul_one]
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add];ring
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg];ring
theorem period_unit_count {a b : CircleHodge.Circle} (p : Trace a b) : period p unitCochain=(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change (1 : ℝ)=((1 : ℤ) : ℝ);norm_num
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add]
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg]
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
theorem actual_lift_on_interval (L : ACLift) (t : unitInterval) : circleLift (projectedLoop L) t=L.val (t : ℝ) := by
  let F : C(unitInterval,ℝ) := ⟨fun t => L.val (t : ℝ),
    L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)⟩
  have h : F=circleLift (projectedLoop L) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,L.property.2.1⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f t) h).symm
theorem projected_winding (L : ACLift) : winding (projectedLoop L)=L.val 1 :=
  actual_lift_on_interval L 1
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
end ComputationalHodge.ACLifts
namespace ComputationalHodge.Dirichlet
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Finite squared-speed energy is required; totalized integrals alone do not assert finiteness. -/
def FiniteEnergy (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => (deriv L.val t)^2) volume 0 1
noncomputable def energy (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,(deriv L.val t)^2
noncomputable def defect (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,(deriv L.val t-L.val 1)^2
theorem derivative_integral (L : ACLift) : ∫ t in (0 : ℝ)..1,deriv L.val t=L.val 1 := by
  simpa [L.property.2.1] using L.property.1.integral_deriv_eq_sub
theorem defect_integrable (L : ACLift) (h : FiniteEnergy L) : IntervalIntegrable (fun t => (deriv L.val t-L.val 1)^2) volume 0 1 := by
  convert (h.sub (L.property.1.intervalIntegrable_deriv.const_mul (2*L.val 1))).add
    (intervalIntegrable_const (c := (L.val 1)^2)) using 1
  ext t
  ring
theorem energy_splitting (L : ACLift) (h : FiniteEnergy L) : energy L=(L.val 1)^2+defect L := by
  have he : (fun t => (deriv L.val t-L.val 1)^2)=
      fun t => (deriv L.val t)^2-(2*L.val 1)*deriv L.val t+(L.val 1)^2 := by
    funext t;ring
  unfold defect
  rw [he,intervalIntegral.integral_add
    (h.sub (L.property.1.intervalIntegrable_deriv.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub h (L.property.1.intervalIntegrable_deriv.const_mul _),
    intervalIntegral.integral_const_mul,derivative_integral]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  unfold energy;ring
theorem energy_lower_bound (L : ACLift) (h : FiniteEnergy L) : (L.val 1)^2≤energy L := by
  rw [energy_splitting L h]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _))
theorem minimum_implies_affine (L : ACLift) (h : FiniteEnergy L) (he : energy L=(L.val 1)^2) : ∀ t∈Icc (0 : ℝ) 1,L.val t=L.val 1*t := by
  have hd : defect L=0 := by have hs := energy_splitting L h;rw [he] at hs;linarith only [hs]
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Filter.Eventually.of_forall (fun t => sq_nonneg (deriv L.val t-L.val 1)))
    (defect_integrable L h)).mp hd
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hz
  have hg : ∀ᵐ t : ℝ,t∈uIcc (0 : ℝ) 1 → deriv L.val t=L.val 1 := by
    rw [uIcc_of_le zero_le_one]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hz] with t ht
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ht)
  have hac : AbsolutelyContinuousOnInterval (fun t => L.val t-L.val 1*t) 0 1 :=
    L.property.1.fun_sub
      ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1))
  have hh : ∀ᵐ t : ℝ,t∈uIcc (0 : ℝ) 1 → HasDerivAt (fun x => L.val x-L.val 1*x) 0 t := by
    filter_upwards [L.property.1.ae_differentiableAt,hg] with t ht hd hm
    simpa only [id_eq,mul_one,hd hm,sub_self] using (ht hm).hasDerivAt.fun_sub ((hasDerivAt_id t).const_mul (L.val 1))
  obtain ⟨C,hC⟩ := hac.const_of_ae_hasDerivAt_zero hh
  have hc : C=0 := by simpa [L.property.2.1] using (hC 0 (by norm_num [uIcc_of_le zero_le_one])).symm
  intro t ht
  have hp := hC t (by simpa [uIcc_of_le zero_le_one] using ht)
  rw [hc] at hp
  exact sub_eq_zero.mp hp
noncomputable def affine (L : ACLift) : ACLift :=
  ⟨fun t => L.val 1*t,
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1),
    by simp,by simpa using L.property.2.2⟩
theorem affine_deriv (L : ACLift) (t : ℝ) : deriv (affine L).val t=L.val 1 := by
  simpa only [affine,id_eq,mul_one] using ((hasDerivAt_id t).const_mul (L.val 1)).deriv
theorem affine_finite (L : ACLift) : FiniteEnergy (affine L) := by
  simpa only [FiniteEnergy,affine_deriv] using
    (intervalIntegrable_const (c := (L.val 1)^2) : IntervalIntegrable _ volume 0 1)
theorem affine_energy (L : ACLift) : energy (affine L)=(L.val 1)^2 := by
  simp [energy,affine_deriv]
theorem energy_congr_on {L M : ACLift} (h : EqOn L.val M.val (Icc 0 1)) : energy L=energy M := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have ht' : t∈Ioo (0 : ℝ) 1 := by simpa [uIoo_of_lt zero_lt_one] using ht
  have he : L.val=ᶠ[nhds t] M.val := by
    filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with x hx
    exact h ⟨hx.1.le,hx.2.le⟩
  exact congrArg (fun x : ℝ => x^2) he.deriv_eq
theorem minimum_iff_affine (L : ACLift) (h : FiniteEnergy L) : energy L=(L.val 1)^2 ↔ EqOn L.val (affine L).val (Icc 0 1) := by
  constructor
  · exact minimum_implies_affine L h
  · intro he;rw [energy_congr_on he,affine_energy]
/-- Actual endpoint-fixed homotopy obtained by linear interpolation of the real lifts. -/
noncomputable def affineHomotopy (L : ACLift) : _root_.Path.Homotopy (projectedLoop L) (projectedLoop (affine L)) where
  toFun st := (((1-(st.1 : ℝ))*L.val (st.2 : ℝ)+(st.1 : ℝ)*(L.val 1*(st.2 : ℝ)) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    have hc : Continuous (fun st : unitInterval×unitInterval => L.val (st.2 : ℝ)) :=
      L.property.1.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_snd)
        (fun st => by simpa only [uIcc_of_le zero_le_one] using st.2.property)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hc).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
  map_zero_left := by intro t;simp [projectedLoop]
  map_one_left := by intro t;simp [projectedLoop,affine]
  prop' := by
    intro s t ht
    rcases ht with ht|ht
    · subst t;simp [projectedLoop,L.property.2.1]
    · have ht' : t=1 := by simpa using ht
      subst t
      change (((1-(s : ℝ))*L.val 1+(s : ℝ)*(L.val 1*1) : ℝ) : CircleHodge.Circle)=((L.val 1 : ℝ) : CircleHodge.Circle)
      congr 1;ring
theorem affine_homotopic (L : ACLift) : _root_.Path.Homotopic (projectedLoop L) (projectedLoop (affine L)) := ⟨affineHomotopy L⟩
theorem class_minimum (L M : ACLift) (h : FiniteEnergy M) (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) : energy (affine L)≤energy M := by
  have he : L.val 1=M.val 1 := by
    rw [← projected_winding,← projected_winding];exact winding_homotopic hm
  rw [affine_energy,he];exact energy_lower_bound M h
theorem fromTrace_finite (p : Trace 0 0) : FiniteEnergy (fromTrace p) := by
  obtain ⟨K,hK⟩ := rawLift_lipschitz p
  rw [← actualLift_eq_rawLift] at hK
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top)
    ((aestronglyMeasurable_deriv (actualLift p) _).pow 2) ((K : ℝ)^2)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn := norm_deriv_le_of_lipschitz (x₀ := t) hK
  change (deriv (actualLift p) t)^2≤(K : ℝ)^2
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
theorem computational_minimum (p : Trace 0 0) : energy (affine (fromTrace p))=(period p unitCochain)^2 := by
  rw [affine_energy,period_unit_count]
  change (actualLift p 1)^2=(count p : ℝ)^2
  rw [actualLift_eq_rawLift,rawLift_one]
end ComputationalHodge.Dirichlet
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
/-- Positive nonconstant continuous density, not a flat rescaling. -/
noncomputable def exampleDensity : Density :=
  ⟨⟨fun q => 2+(AddCircle.toCircle q : ℂ).re,by fun_prop⟩,by
    intro q
    have h : |(AddCircle.toCircle q : ℂ).re|≤1 := by
      simpa using Complex.abs_re_le_norm (AddCircle.toCircle q : ℂ)
    change 0<2+(AddCircle.toCircle q : ℂ).re
    linarith [(abs_le.mp h).1]⟩
theorem example_zero : exampleDensity.val 0=3 := by norm_num [exampleDensity]
theorem example_half : exampleDensity.val ((1/2 : ℝ) : CircleHodge.Circle)=1 := by
  change 2+(AddCircle.toCircle ((1/2 : ℝ) : CircleHodge.Circle) : ℂ).re=1
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  have he : 2*Real.pi*(1/2 : ℝ)=Real.pi := by ring
  norm_num [Complex.exp_re,he]
end ComputationalHodge.MetricHodge
namespace ComputationalHodge.ACLifts
open ComputationalHodge.CircleHodge
open MeasureTheory Set
open scoped NNReal
noncomputable def primitive (α : Coefficient) (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u,cover α x
theorem primitive_hasDerivAt (α : Coefficient) (x : ℝ) : HasDerivAt (primitive α) (cover α x) x :=
  intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cover_continuous α).continuousAt
theorem primitive_lipschitz (α : Coefficient) : ∃ K : ℝ≥0,LipschitzWith K (primitive α) := by
  obtain ⟨C,hC⟩ := (isCompact_range α.continuous).isBounded.exists_norm_le
  have h0 : 0≤C := (norm_nonneg (α 0)).trans (hC _ ⟨0,rfl⟩)
  refine ⟨⟨C,h0⟩,lipschitzWith_of_nnnorm_deriv_le
    (fun x => (primitive_hasDerivAt α x).differentiableAt) (fun x => ?_)⟩
  rw [(primitive_hasDerivAt α x).deriv]
  exact hC _ ⟨(x : CircleHodge.Circle),rfl⟩
theorem primitive_comp_ac (α : Coefficient) (L : ACLift) : AbsolutelyContinuousOnInterval (fun t => primitive α (L.val t)) 0 1 := by
  obtain ⟨K,hK⟩ := primitive_lipschitz α
  exact hK.comp_absolutelyContinuousOnInterval L.property.1
theorem chain_rule_ae (α : Coefficient) (L : ACLift) : ∀ᵐ t : ℝ, t∈uIcc (0 : ℝ) 1 → deriv (fun x => primitive α (L.val x)) t=cover α (L.val t)*deriv L.val t := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hmem
  exact ((primitive_hasDerivAt α (L.val t)).comp t (ht hmem).hasDerivAt).deriv
end ComputationalHodge.ACLifts
namespace ComputationalHodge.Arclength
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.Dirichlet ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval
theorem density_bounds (ρ : Density) : ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ q,c≤ρ.val q ∧ ρ.val q≤C := by
  obtain ⟨c,hc,hlo⟩ := isCompact_univ.exists_forall_le'
    ρ.val.continuous.continuousOn (fun q _ => ρ.property q)
  obtain ⟨C,hC⟩ := (isCompact_range ρ.val.continuous).isBounded.exists_norm_le
  have hupper (q : CircleHodge.Circle) : ρ.val q≤C :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC _ ⟨q,rfl⟩)
  exact ⟨c,C,hc,(ρ.property 0).trans_le (hupper 0),fun q => ⟨hlo q (mem_univ _),hupper q⟩⟩
noncomputable def coordinate (ρ : Density) (x : ℝ) : ℝ := primitive ρ.val x/mean ρ.val
theorem coordinate_hasDerivAt (ρ : Density) (x : ℝ) : HasDerivAt (coordinate ρ) (cover ρ.val x/mean ρ.val) x :=
  (primitive_hasDerivAt ρ.val x).div_const _
theorem coordinate_zero (ρ : Density) : coordinate ρ 0=0 := by simp [coordinate,primitive]
theorem coordinate_lipschitz (ρ : Density) : ∃ K : ℝ≥0,LipschitzWith K (coordinate ρ) := by
  obtain ⟨_,C,_,hC,hbound⟩:=density_bounds ρ
  refine ⟨⟨C/mean ρ.val,(div_pos hC (mean_pos ρ)).le⟩,
    lipschitzWith_of_nnnorm_deriv_le (fun x => (coordinate_hasDerivAt ρ x).differentiableAt) (fun x => ?_)⟩
  rw [(coordinate_hasDerivAt ρ x).deriv]
  change ‖ρ.val (x : CircleHodge.Circle)/mean ρ.val‖≤C/mean ρ.val
  rw [Real.norm_eq_abs,abs_of_pos (div_pos (ρ.property (x : CircleHodge.Circle)) (mean_pos ρ))]
  exact div_le_div_of_nonneg_right (hbound (x : CircleHodge.Circle)).2 (mean_pos ρ).le
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
theorem inverse_zero (ρ : Density) : inverse ρ 0=0 := by
  apply (coordinate_strictMono ρ).injective
  rw [coordinate_inverse,coordinate_zero]
theorem inverse_int (ρ : Density) (n : ℤ) : inverse ρ (n : ℝ)=n := by
  apply (coordinate_strictMono ρ).injective
  rw [coordinate_inverse,coordinate_int]
theorem inverse_hasDerivAt (ρ : Density) (x : ℝ) : HasDerivAt (inverse ρ) (mean ρ.val/cover ρ.val (inverse ρ x)) x := by
  have h := HasDerivAt.of_local_left_inverse
    (coordinateHomeomorph ρ).symm.continuous.continuousAt
    (coordinate_hasDerivAt ρ (inverse ρ x))
    (ne_of_gt (div_pos (ρ.property _) (mean_pos ρ)))
    (Filter.Eventually.of_forall (coordinate_inverse ρ))
  simpa only [inverse,inv_div] using h
theorem inverse_lipschitz (ρ : Density) : ∃ K : ℝ≥0,LipschitzWith K (inverse ρ) := by
  obtain ⟨c,C,hc,_,hbound⟩:=density_bounds ρ
  refine ⟨⟨mean ρ.val/c,(div_pos (mean_pos ρ) hc).le⟩,
    lipschitzWith_of_nnnorm_deriv_le (fun x => (inverse_hasDerivAt ρ x).differentiableAt) (fun x => ?_)⟩
  rw [(inverse_hasDerivAt ρ x).deriv]
  change ‖mean ρ.val/ρ.val ((inverse ρ x : ℝ) : CircleHodge.Circle)‖≤mean ρ.val/c
  rw [Real.norm_eq_abs,abs_of_pos (div_pos (mean_pos ρ) (ρ.property ((inverse ρ x : ℝ) : CircleHodge.Circle)))]
  exact div_le_div_of_nonneg_left (mean_pos ρ).le hc (hbound ((inverse ρ x : ℝ) : CircleHodge.Circle)).1
theorem coordinate_endpoint (ρ : Density) (L : ACLift) : coordinate ρ (L.val 1)=L.val 1 := by
  obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
  have he : (n : ℝ)=L.val 1 := by simpa using hn
  rw [← he,coordinate_int]
noncomputable def transformed (ρ : Density) (L : ACLift) : ACLift :=
  ⟨fun t => coordinate ρ (L.val t),by
    obtain ⟨K,hK⟩:=coordinate_lipschitz ρ
    exact hK.comp_absolutelyContinuousOnInterval L.property.1,
    by change coordinate ρ (L.val 0)=0;rw [L.property.2.1,coordinate_zero],
    by change ((coordinate ρ (L.val 1) : ℝ) : CircleHodge.Circle)=0;rw [coordinate_endpoint];exact L.property.2.2⟩
theorem transformed_endpoint (ρ : Density) (L : ACLift) : (transformed ρ L).val 1=L.val 1 :=
  coordinate_endpoint ρ L
noncomputable def minimizer (ρ : Density) (L : ACLift) : ACLift :=
  ⟨fun t => inverse ρ (L.val 1*t),by
    obtain ⟨K,hK⟩:=inverse_lipschitz ρ
    exact hK.comp_absolutelyContinuousOnInterval
      ((LipschitzWith.id : LipschitzWith 1 (id : ℝ→ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1)),
    by simp [inverse_zero],by
      obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
      have he : (n : ℝ)=L.val 1 := by simpa using hn
      simp only [mul_one]
      rw [← he,inverse_int]
      simp⟩
theorem minimizer_endpoint (ρ : Density) (L : ACLift) : (minimizer ρ L).val 1=L.val 1 := by
  obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
  have he : (n : ℝ)=L.val 1 := by simpa using hn
  change inverse ρ (L.val 1*1)=L.val 1
  rw [mul_one,← he,inverse_int]
theorem transformed_minimizer (ρ : Density) (L : ACLift) : transformed ρ (minimizer ρ L)=affine L := by
  apply Subtype.ext
  funext t
  exact coordinate_inverse ρ (L.val 1*t)
/-- The actual squared speed for the circle length convention ds=ρ dx; no factor 1/2. -/
noncomputable def energy (ρ : Density) (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,(cover ρ.val (L.val t)*deriv L.val t)^2
def WeightedFiniteEnergy (ρ : Density) (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => (cover ρ.val (L.val t)*deriv L.val t)^2) volume 0 1
theorem square_ae (ρ : Density) (L : ACLift) : ∀ᵐ t : ℝ,t∈uIoc (0 : ℝ) 1 → (cover ρ.val (L.val t)*deriv L.val t)^2= (mean ρ.val)^2*(deriv (transformed ρ L).val t)^2 := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hm
  have hm' : t∈uIcc (0 : ℝ) 1 := by
    simp only [uIoc_of_le zero_le_one] at hm
    simpa only [uIcc_of_le zero_le_one] using (show t∈Icc (0 : ℝ) 1 from ⟨hm.1.le,hm.2⟩)
  have hd := ((coordinate_hasDerivAt ρ (L.val t)).comp t (ht hm').hasDerivAt).deriv
  change deriv (transformed ρ L).val t=(cover ρ.val (L.val t)/mean ρ.val)*deriv L.val t at hd
  rw [hd]
  field_simp [ne_of_gt (mean_pos ρ)]
theorem energy_identity (ρ : Density) (L : ACLift) : energy ρ L=(mean ρ.val)^2*Dirichlet.energy (transformed ρ L) := by
  unfold energy Dirichlet.energy
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae (square_ae ρ L)
theorem finite_iff (ρ : Density) (L : ACLift) : WeightedFiniteEnergy ρ L ↔ Dirichlet.FiniteEnergy (transformed ρ L) := by
  have he : (fun t => (cover ρ.val (L.val t)*deriv L.val t)^2)=ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun t => (mean ρ.val)^2*(deriv (transformed ρ L).val t)^2) :=
    (ae_restrict_iff' measurableSet_uIoc).mpr (square_ae ρ L)
  constructor
  · intro h
    have hh : Dirichlet.FiniteEnergy (transformed ρ L) :=
      (h.const_mul ((mean ρ.val)^2)⁻¹).congr_ae ?_
    · exact hh
    filter_upwards [he] with t ht
    rw [ht]
    field_simp [ne_of_gt (mean_pos ρ)]
  · intro h
    exact (h.const_mul ((mean ρ.val)^2)).congr_ae he.symm
theorem minimizer_finite (ρ : Density) (L : ACLift) : WeightedFiniteEnergy ρ (minimizer ρ L) := by
  rw [finite_iff,transformed_minimizer]
  exact affine_finite L
theorem minimizer_energy (ρ : Density) (L : ACLift) : energy ρ (minimizer ρ L)=(mean ρ.val*L.val 1)^2 := by
  rw [energy_identity,transformed_minimizer,affine_energy]
  ring
theorem energy_lower_bound (ρ : Density) (L : ACLift) (h : WeightedFiniteEnergy ρ L) : (mean ρ.val*L.val 1)^2≤energy ρ L := by
  rw [energy_identity,mul_pow]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [transformed_endpoint] using Dirichlet.energy_lower_bound (transformed ρ L) ((finite_iff ρ L).mp h))
    (sq_nonneg _)
theorem minimum_iff (ρ : Density) (L : ACLift) (h : WeightedFiniteEnergy ρ L) : energy ρ L=(mean ρ.val*L.val 1)^2 ↔ EqOn L.val (minimizer ρ L).val (Icc 0 1) := by
  rw [energy_identity,mul_pow,mul_eq_mul_left_iff]
  have hn : (mean ρ.val)^2≠0 := pow_ne_zero 2 (ne_of_gt (mean_pos ρ))
  simp only [hn,or_false]
  rw [← transformed_endpoint ρ L,minimum_iff_affine _ ((finite_iff ρ L).mp h)]
  constructor
  · intro he t ht
    apply (coordinate_strictMono ρ).injective
    have hh := he ht
    change coordinate ρ (L.val t)=(transformed ρ L).val 1*t at hh
    rw [transformed_endpoint] at hh
    exact hh.trans (coordinate_inverse ρ (L.val 1*t)).symm
  · intro he t ht
    change coordinate ρ (L.val t)=(transformed ρ L).val 1*t
    rw [transformed_endpoint,he ht]
    exact coordinate_inverse ρ (L.val 1*t)
theorem minimizer_homotopic (ρ : Density) (L : ACLift) : _root_.Path.Homotopic (projectedLoop L) (projectedLoop (minimizer ρ L)) := by
  have he : affine L=affine (minimizer ρ L) := by
    apply Subtype.ext
    funext t
    change L.val 1*t=(minimizer ρ L).val 1*t
    rw [minimizer_endpoint]
  exact (affine_homotopic L).trans (by rw [he];exact (affine_homotopic (minimizer ρ L)).symm)
theorem finite_of_lipschitz (ρ : Density) (L : ACLift) {K : ℝ≥0} (hL : LipschitzWith K L.val) : WeightedFiniteEnergy ρ L := by
  rw [finite_iff]
  obtain ⟨C,hC⟩:=coordinate_lipschitz ρ
  have hK : LipschitzWith (C*K) (transformed ρ L).val := hC.comp hL
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top)
    ((aestronglyMeasurable_deriv (transformed ρ L).val _).pow 2) (((C*K : ℝ≥0) : ℝ)^2)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn := norm_deriv_le_of_lipschitz (x₀:=t) hK
  change (deriv (transformed ρ L).val t)^2≤((C*K : ℝ≥0) : ℝ)^2
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
theorem fromTrace_finite (ρ : Density) (p : Trace 0 0) : WeightedFiniteEnergy ρ (fromTrace p) := by
  obtain ⟨K,hK⟩:=rawLift_lipschitz p
  rw [← actualLift_eq_rawLift] at hK
  exact finite_of_lipschitz ρ (fromTrace p) hK
theorem class_minimum (ρ : Density) (L M : ACLift) (h : WeightedFiniteEnergy ρ M) (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) : energy ρ (minimizer ρ L)≤energy ρ M := by
  have he : L.val 1=M.val 1 := by
    rw [← projected_winding,← projected_winding];exact winding_homotopic hm
  rw [minimizer_energy,he]
  exact energy_lower_bound ρ M h
theorem computational_minimum (ρ : Density) (p : Trace 0 0) : energy ρ (minimizer ρ (fromTrace p))=(period p (meanHarmonic ρ.val).val)^2 := by
  rw [minimizer_energy]
  change (mean ρ.val*actualLift p 1)^2=(period p (meanCochain ρ.val))^2
  rw [actualLift_eq_rawLift,rawLift_one,period_mean_count]
theorem class_minimum_iff (ρ : Density) (L M : ACLift) (h : WeightedFiniteEnergy ρ M) (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) : energy ρ M=energy ρ (minimizer ρ L) ↔ EqOn M.val (minimizer ρ L).val (Icc 0 1) := by
  have he : M.val 1=L.val 1 := by
    rw [← projected_winding,← projected_winding];exact (winding_homotopic hm).symm
  have hh : minimizer ρ M=minimizer ρ L := by
    apply Subtype.ext
    funext t
    change inverse ρ (M.val 1*t)=inverse ρ (L.val 1*t)
    rw [he]
  rw [← hh,minimizer_energy]
  exact minimum_iff ρ M h
noncomputable def unitLift : ACLift :=
  ⟨id,(LipschitzWith.id : LipschitzWith 1 (id : ℝ→ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval,
    rfl,by simp⟩
theorem unitLift_finite (ρ : Density) : WeightedFiniteEnergy ρ unitLift :=
  finite_of_lipschitz ρ unitLift LipschitzWith.id
theorem unit_minimum_forces_density (ρ : Density) (he : energy ρ unitLift=(mean ρ.val)^2) (x : ℝ) (hx : x∈Ioo (0 : ℝ) 1) : cover ρ.val x=mean ρ.val := by
  have he' : energy ρ unitLift=(mean ρ.val*unitLift.val 1)^2 := by simpa [unitLift] using he
  have hh := (minimum_iff ρ unitLift (unitLift_finite ρ)).mp he'
  have hc (y : ℝ) (hy : y∈Icc (0 : ℝ) 1) : coordinate ρ y=y := by
    have h := congrArg (coordinate ρ) (hh hy)
    change coordinate ρ y=coordinate ρ (inverse ρ (1*y)) at h
    simpa only [one_mul,coordinate_inverse] using h
  have hf : coordinate ρ=ᶠ[nhds x] id := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hc y ⟨hy.1.le,hy.2.le⟩
  have hd : cover ρ.val x/mean ρ.val=1 := by
    rw [← (coordinate_hasDerivAt ρ x).deriv,hf.deriv_eq]
    exact deriv_id x
  exact (div_eq_iff (ne_of_gt (mean_pos ρ))).mp hd |>.trans (one_mul _)
theorem example_quarter : exampleDensity.val ((1/4 : ℝ) : CircleHodge.Circle)=2 := by
  change 2+(AddCircle.toCircle ((1/4 : ℝ) : CircleHodge.Circle) : ℂ).re=2
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  have he : 2*Real.pi*(1/4 : ℝ)=Real.pi/2 := by ring
  norm_num [Complex.exp_re,he]
/-- A nonconstant metric has a strictly better admitted path than the flat affine unit loop. -/
theorem example_strict : energy exampleDensity (minimizer exampleDensity unitLift)< energy exampleDensity unitLift := by
  apply lt_of_le_of_ne
  · rw [minimizer_energy]
    exact energy_lower_bound exampleDensity unitLift (unitLift_finite exampleDensity)
  · intro he
    have hh : energy exampleDensity unitLift=(mean exampleDensity.val)^2 := by
      rw [← he,minimizer_energy];simp [unitLift]
    have hq:=unit_minimum_forces_density exampleDensity hh (1/4) (by norm_num)
    have hr:=unit_minimum_forces_density exampleDensity hh (1/2) (by norm_num)
    change exampleDensity.val ((1/4 : ℝ) : CircleHodge.Circle)=_ at hq
    change exampleDensity.val ((1/2 : ℝ) : CircleHodge.Circle)=_ at hr
    rw [example_quarter] at hq
    rw [example_half] at hr
    linarith
end ComputationalHodge.Arclength
