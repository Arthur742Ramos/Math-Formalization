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
  induction p with
  | refl a => intro t; simp [rawLift]
  | single s =>
    intro t; constructor
    · intro ht
      simp [rawLift,clamp,min_eq_right (show t ≤ (1 : ℝ) by linarith),max_eq_left ht]
    · intro ht
      simp [rawLift,clamp,min_eq_left ht]
  | trans p q hp hq =>
    intro t; constructor
    · intro ht
      simpa only [rawLift, ite_eq_left (show t ≤ (1 : ℝ)/2 by linarith)] using
        (hp (2*t)).1 (by linarith)
    · intro ht
      change (if t ≤ (1 : ℝ)/2 then rawLift p (2*t) else rawLift p 1 + rawLift q (2*t-1)) =
        (if (1 : ℝ) ≤ (1 : ℝ)/2 then rawLift p (2*1) else rawLift p 1 + rawLift q (2*1-1))
      rw [ite_eq_right (show ¬ t ≤ (1 : ℝ)/2 by linarith),
        ite_eq_right (show ¬ (1 : ℝ) ≤ 1/2 by norm_num), (hq (2*t-1)).2 (by linarith)]
      norm_num
  | symm p hp =>
    intro t; constructor
    · intro ht
      simpa only [rawLift,sub_self] using sub_eq_zero.mpr ((hp (1-t)).2 (by linarith))
    · intro ht
      simp only [rawLift,sub_self,(hp (1-t)).1 (by linarith),rawLift_zero]
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
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/
noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
end ComputationalHodge.GreenOperator
namespace ComputationalHodge.ResonanceObstruction
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
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
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.GreenOperator
open ComputationalHodge.ResonanceObstruction ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters
noncomputable def curvedFrequency (ρ : RegularDensity) (n : ℕ) : ℝ :=
  (mean ρ.val.val)⁻¹ ^ 2 * frequencyN n
noncomputable def curvedCosine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (cosineNC2 n)
noncomputable def curvedSine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (sineNC2 n)
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.DirectResonancePrototype
open ComputationalHodge.CircleHodge ComputationalHodge.ACLifts
open ComputationalHodge.ArclengthSpectrum
open MeasureTheory Set
theorem primitive_periodic_of_zero (α : Coefficient) (hmean : mean α = 0) : Function.Periodic (primitive α) 1 := by
  intro x
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq (1 : ℤ) x
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  rw [(cover_periodic α).intervalIntegral_add_eq x 0] at h
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_one] at h
  have ha := intervalIntegral.integral_add_adjacent_intervals
    ((cover_continuous α).intervalIntegrable (μ:=volume) 0 x)
    ((cover_continuous α).intervalIntegrable (μ:=volume) x (x+1))
  unfold primitive
  rw [← ha, h]
  simp only [one_mul]
  change _ + mean α = _
  rw [hmean, add_zero]
open ComputationalHodge.Poisson ComputationalHodge.ResonanceObstruction
open scoped ContDiff
theorem primitive_contDiff_one (α : Coefficient) : ContDiff ℝ 1 (primitive α) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (primitive_hasDerivAt α x).differentiableAt, ?_⟩
  have h : deriv (primitive α) = cover α := funext fun x => (primitive_hasDerivAt α x).deriv
  rw [h]
  exact cover_continuous α
end ComputationalHodge.DirectResonancePrototype
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.Arclength ComputationalHodge.ResonanceObstruction
open scoped ContDiff
open ComputationalHodge.ACLifts ComputationalHodge.GreenOperator
open MeasureTheory Set
end ComputationalHodge.ArclengthSpectrum
namespace ComputationalHodge.ResonantPeriodsPrototype
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.GreenOperator
open ComputationalHodge.ResonanceObstruction ComputationalHodge.ACLifts
open ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open ComputationalHodge.ArclengthSpectrum
theorem pairing_implies_trace (ρ : RegularDensity) (f v : Coefficient) (h : pairing ρ f v = 0) (p : Trace 0 0) : lineIntegral (ρ.val.val * f * v) (fromTrace p) = 0 := by
  rw [lineIntegral_eq_mean]
  change pairing ρ f v * (fromTrace p).val 1 = 0
  rw [h, zero_mul]
def unitTrace : Trace 0 0 := .single ()
theorem unit_trace_integral (α : Coefficient) : lineIntegral α (fromTrace unitTrace) = mean α := by
  rw [lineIntegral_eq_mean]
  change mean α * actualLift unitTrace 1 = mean α
  rw [actualLift_eq_rawLift, rawLift_one]
  simp [unitTrace, count]
theorem trace_periods_iff_pairing (ρ : RegularDensity) (f v : Coefficient) : (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * v) (fromTrace p) = 0) ↔ pairing ρ f v = 0 := by
  constructor
  · intro hp
    have h := hp unitTrace
    rw [unit_trace_integral] at h
    exact h
  · intro h p
    exact pairing_implies_trace ρ f v h p
theorem cochain_periods_iff_pairing (ρ : RegularDensity) (f v : Coefficient) : (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * v)).val = 0) ↔ pairing ρ f v = 0 := by
  simpa only [lineIntegral_fromTrace_harmonic] using trace_periods_iff_pairing ρ f v
end ComputationalHodge.ResonantPeriodsPrototype
namespace ComputationalHodge.ResonantPeriodsPrototype
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.ResonanceObstruction ComputationalHodge.GreenOperator
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.ArclengthSpectrum
theorem wronskian_derivative (U Q C S : ℝ → ℝ) (ρ F : ℝ → ℝ) (k x : ℝ)
    (hU : HasDerivAt U (ρ x * Q x) x)
    (hQ : HasDerivAt Q (-ρ x * (k ^ 2 * U x + F x)) x)
    (hC : HasDerivAt C (-k * ρ x * S x) x)
    (hS : HasDerivAt S (k * ρ x * C x) x) :
    HasDerivAt (fun t => Q t * C t + k * U t * S t) (-(ρ x * F x * C x)) x := by
  have h := (hQ.mul hC).add ((hU.mul hS).const_mul k)
  convert h using 1
  · funext t; simp only [Pi.add_apply, Pi.mul_apply]; ring
  · ring

theorem wronskian_integral_zero (U Q C S ρ F : ℝ → ℝ) (k : ℝ)
    (hU : ∀ x, HasDerivAt U (ρ x * Q x) x)
    (hQ : ∀ x, HasDerivAt Q (-ρ x * (k ^ 2 * U x + F x)) x)
    (hC : ∀ x, HasDerivAt C (-k * ρ x * S x) x)
    (hS : ∀ x, HasDerivAt S (k * ρ x * C x) x)
    (hc : Continuous (fun x => ρ x * F x * C x))
    (hp : Q 1 * C 1 + k * U 1 * S 1 = Q 0 * C 0 + k * U 0 * S 0) :
    (∫ x in (0 : ℝ)..1, ρ x * F x * C x) = 0 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => wronskian_derivative U Q C S ρ F k x (hU x) (hQ x) (hC x) (hS x))
    (hc.neg.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_neg, hp, sub_self, neg_eq_zero] at hi
  exact hi


theorem wronskian_pair (U Q C S R F : ℝ → ℝ) (k : ℝ)
    (hU : ∀ x, HasDerivAt U (R x * Q x) x)
    (hQ : ∀ x, HasDerivAt Q (-R x * (k ^ 2 * U x + F x)) x)
    (hC : ∀ x, HasDerivAt C (-k * R x * S x) x)
    (hS : ∀ x, HasDerivAt S (k * R x * C x) x)
    (hc : Continuous (fun x => R x * F x * C x)) (hs : Continuous (fun x => R x * F x * S x))
    (hu : U 1 = U 0) (hq : Q 1 = Q 0) (hcx : C 1 = C 0) (hsx : S 1 = S 0) :
    (∫ x in (0 : ℝ)..1, R x * F x * C x) = 0 ∧ (∫ x in (0 : ℝ)..1, R x * F x * S x) = 0 := by
  have hp : Q 1 * C 1 + k * U 1 * S 1 = Q 0 * C 0 + k * U 0 * S 0 := by rw [hu, hq, hcx, hsx]
  have h := wronskian_integral_zero U Q C S R F k hU hQ hC hS hc hp
  have hCS (x : ℝ) : HasDerivAt S (-k * R x * (-C x)) x := by
    convert hS x using 1; ring
  have hSC (x : ℝ) : HasDerivAt (fun x => -C x) (k * R x * S x) x := by
    convert (hC x).neg using 1; ring
  have hps : Q 1 * S 1 + k * U 1 * (-C 1) = Q 0 * S 0 + k * U 0 * (-C 0) := by rw [hu, hq, hcx, hsx]
  exact ⟨h, wronskian_integral_zero U Q S (fun x => -C x) R F k hU hQ hCS hSC hs hps⟩

open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.GreenOperator ComputationalHodge.ArclengthSpectrum

theorem curved_mode_data (ρ : RegularDensity) (n : ℕ) :
    (∀ x, HasDerivAt (cover (curvedCosine ρ n).val)
      (-(angular n / mean ρ.val.val) * cover ρ.val.val x * cover (curvedSine ρ n).val x) x) ∧
    (∀ x, HasDerivAt (cover (curvedSine ρ n).val)
      ((angular n / mean ρ.val.val) * cover ρ.val.val x * cover (curvedCosine ρ n).val x) x) ∧
    (∀ x, cover (curvedCosine ρ n).val x ^ 2 + cover (curvedSine ρ n).val x ^ 2 = 1) := by
  let C := cover (curvedCosine ρ n).val
  let S := cover (curvedSine ρ n).val
  have hcval (x : ℝ) : C x = Real.cos (angular n * coordinate ρ.val x) := by
    change cover (pullback ρ (cosineN n)) x = _
    simp only [cover_pullback, cosineN_cover, angular, mul_assoc]
  have hsval (x : ℝ) : S x = Real.sin (angular n * coordinate ρ.val x) := by
    change cover (pullback ρ (sineN n)) x = _
    simp only [cover_pullback, sineN_cover, angular, mul_assoc]
  let R := cover ρ.val.val
  let k := angular n / mean ρ.val.val
  have hC (x : ℝ) : HasDerivAt C (-k * R x * S x) x := by
    have h := ((coordinate_hasDerivAt ρ.val x).const_mul (angular n)).cos
    rw [show C = (fun t => Real.cos (angular n * coordinate ρ.val t)) from funext hcval, hsval x]
    dsimp [k, R]
    convert h using 1; ring
  have hS (x : ℝ) : HasDerivAt S (k * R x * C x) x := by
    have h := ((coordinate_hasDerivAt ρ.val x).const_mul (angular n)).sin
    rw [show S = (fun t => Real.sin (angular n * coordinate ρ.val t)) from funext hsval, hcval x]
    dsimp [k, R]
    convert h using 1; ring
  refine ⟨hC,hS,?_⟩
  intro x
  change C x ^ 2 + S x ^ 2 = 1
  rw [hcval, hsval]
  nlinarith [Real.sin_sq_add_cos_sq (angular n * coordinate ρ.val x)]

theorem mode_pairings (ρ : RegularDensity) (n : ℕ) (u : C2Coefficient) (f : Coefficient)
    (hu : laplacian ρ u - curvedFrequency ρ n • u.val = f) :
    pairing ρ f (curvedCosine ρ n).val = 0 ∧ pairing ρ f (curvedSine ρ n).val = 0 := by
  let R := cover ρ.val.val
  let U := cover u.val
  let Q := cover (flux ρ u)
  let F := cover f
  let k := angular n / mean ρ.val.val
  have hm : mean ρ.val.val ≠ 0 := ne_of_gt (mean_pos ρ.val)
  have hR (x : ℝ) : R x ≠ 0 := density_ne ρ.val (x : CircleHodge.Circle)
  have hk : k ^ 2 = curvedFrequency ρ n := by
    dsimp [k, curvedFrequency, frequencyN]
    field_simp [hm]
  have hU (x : ℝ) : HasDerivAt U (R x * Q x) x := by
    have h := ((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x).hasDerivAt
    convert h using 1
    change cover ρ.val.val x * (deriv (cover u.val) x / cover ρ.val.val x) = _
    field_simp [show cover ρ.val.val x ≠ 0 from density_ne ρ.val (x : CircleHodge.Circle)]
  have hQ (x : ℝ) : HasDerivAt Q (-R x * (k ^ 2 * U x + F x)) x := by
    have h := ((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt
    have he := congrArg (fun g : Coefficient => cover g x) hu
    change -(deriv Q x) / R x - curvedFrequency ρ n * U x = F x at he
    convert h using 1
    rw [hk]
    field_simp [hR x] at he ⊢
    linarith
  clear hu hm hR hk
  let C := cover (curvedCosine ρ n).val
  let S := cover (curvedSine ρ n).val
  obtain ⟨hC,hS,_⟩ := curved_mode_data ρ n
  have hc : Continuous (fun x => R x * F x * C x) :=
    (cover_continuous ρ.val.val).mul (cover_continuous f) |>.mul (cover_continuous (curvedCosine ρ n).val)
  have hu0 : U 1 = U 0 := by simpa only [zero_add] using cover_periodic u.val 0
  have hq0 : Q 1 = Q 0 := by simpa only [zero_add] using cover_periodic (flux ρ u) 0
  have hc0 : C 1 = C 0 := by simpa only [zero_add] using cover_periodic (curvedCosine ρ n).val 0
  have hs0 : S 1 = S 0 := by simpa only [zero_add] using cover_periodic (curvedSine ρ n).val 0
  have hs : Continuous (fun x => R x * F x * S x) :=
    (cover_continuous ρ.val.val).mul (cover_continuous f) |>.mul (cover_continuous (curvedSine ρ n).val)
  exact wronskian_pair U Q C S R F k hU hQ hC hS hc hs hu0 hq0 hc0 hs0


open ComputationalHodge.DirectResonancePrototype
open scoped ContDiff
noncomputable def weightedSolution (k : ℝ) (A B C S : ℝ → ℝ) (x : ℝ) : ℝ :=
  (C x * B x - S x * A x) / k

def weightedFlux (A B C S : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(S x * B x + C x * A x)

theorem weighted_solution_derivatives (A B C S R F : ℝ → ℝ) (k x : ℝ)
    (hk : k ≠ 0) (hunit : C x ^ 2 + S x ^ 2 = 1)
    (hA : HasDerivAt A (R x * F x * C x) x)
    (hB : HasDerivAt B (R x * F x * S x) x)
    (hC : HasDerivAt C (-k * R x * S x) x)
    (hS : HasDerivAt S (k * R x * C x) x) :
    HasDerivAt (weightedSolution k A B C S) (R x * weightedFlux A B C S x) x ∧
    HasDerivAt (weightedFlux A B C S) (-R x * (k ^ 2 * weightedSolution k A B C S x + F x)) x := by
  constructor
  · have h := ((hC.mul hB).sub (hS.mul hA)).div_const k
    convert h using 1
    · rfl
    · dsimp [weightedFlux]
      field_simp
      ring
  · have h := ((hS.mul hB).add (hC.mul hA)).neg
    convert h using 1
    · rfl
    · dsimp [weightedSolution]
      field_simp [hk]
      have hc : R x * F x * (C x ^ 2 + S x ^ 2) = R x * F x := by rw [hunit]; ring
      nlinarith [hc]


theorem solution_from_cover (ρ : RegularDensity) (f : Coefficient) (lam : ℝ) (U Q : ℝ → ℝ)
    (hU : ∀ x, HasDerivAt U (cover ρ.val.val x * Q x) x)
    (hQ : ∀ x, HasDerivAt Q (-cover ρ.val.val x * (lam * U x + cover f x)) x)
    (hu2 : ContDiff ℝ 2 U) (hup : Function.Periodic U 1) :
    ∃ u : C2Coefficient, laplacian ρ u - lam • u.val = f := by
  have hderiv : deriv U = fun x => cover ρ.val.val x * Q x := funext fun x => (hU x).deriv
  let u : Coefficient := ⟨hup.lift, hu2.continuous.quotient_liftOn' _⟩
  let u2 : C2Coefficient := ⟨u,hu2⟩
  refine ⟨u2,?_⟩
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian ρ u2) x - lam * U x = cover f x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv U t / cover ρ.val.val t) x) / cover ρ.val.val x - lam * U x = cover f x
  have hf : (fun t => deriv U t / cover ρ.val.val t) = Q := by
    funext t
    rw [hderiv]
    field_simp [show cover ρ.val.val t ≠ 0 from density_ne ρ.val (t : CircleHodge.Circle)]
  rw [hf, (hQ x).deriv]
  field_simp [show cover ρ.val.val x ≠ 0 from density_ne ρ.val (x : CircleHodge.Circle)]
  ring

theorem solution_c2 (R U Q : ℝ → ℝ) (hR : ContDiff ℝ 1 R) (hQ : ContDiff ℝ 1 Q)
    (hU : ∀ x, HasDerivAt U (R x * Q x) x) : ContDiff ℝ 2 U := by
  have hderiv : deriv U = fun x => R x * Q x := funext fun x => (hU x).deriv
  change ContDiff ℝ ((1 : ℕ∞ω)+1) U
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (hU x).differentiableAt, by norm_num, ?_⟩
  rw [hderiv]
  exact hR.mul hQ

theorem weighted_direct_solution (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient)
    (hc : pairing ρ f (curvedCosine ρ n).val = 0)
    (hs : pairing ρ f (curvedSine ρ n).val = 0) :
    ∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = f := by
  let k := angular n / mean ρ.val.val
  have hm : mean ρ.val.val ≠ 0 := ne_of_gt (mean_pos ρ.val)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : angular n ≠ 0 := by unfold angular; positivity
  have hk : k ≠ 0 := div_ne_zero ha hm
  have hk2 : k ^ 2 = curvedFrequency ρ n := by
    dsimp [k, curvedFrequency, frequencyN]
    field_simp [hm]
  let R := cover ρ.val.val
  let F := cover f
  let C := cover (curvedCosine ρ n).val
  let S := cover (curvedSine ρ n).val
  let A := primitive (ρ.val.val * f * (curvedCosine ρ n).val)
  let B := primitive (ρ.val.val * f * (curvedSine ρ n).val)
  have hmode := curved_mode_data ρ n
  let U := weightedSolution k A B C S
  let Q := weightedFlux A B C S
  have hdu (x : ℝ) := weighted_solution_derivatives A B C S R F k x hk (hmode.2.2 x)
    (primitive_hasDerivAt (ρ.val.val * f * (curvedCosine ρ n).val) x)
    (primitive_hasDerivAt (ρ.val.val * f * (curvedSine ρ n).val) x) (hmode.1 x) (hmode.2.1 x)
  clear hmode hn hn' ha hk hm
  have hQ1 : ContDiff ℝ 1 Q := by
    dsimp [Q, weightedFlux]
    exact (((c2_c1 (curvedSine ρ n)).mul (primitive_contDiff_one _)).add
      ((c2_c1 (curvedCosine ρ n)).mul (primitive_contDiff_one _))).neg
  have hu2 : ContDiff ℝ 2 U := solution_c2 R U Q ρ.property hQ1 (fun x => (hdu x).1)
  clear hQ1
  have hup : Function.Periodic U 1 := by
    change Function.Periodic ((C * B - S * A) / fun _ => k) 1
    exact (((cover_periodic (curvedCosine ρ n).val).mul (primitive_periodic_of_zero _ hs)).sub
      ((cover_periodic (curvedSine ρ n).val).mul (primitive_periodic_of_zero _ hc))).div (fun _ => rfl)
  clear hc hs
  rw [← hk2]
  exact solution_from_cover ρ f (k ^ 2) U Q (fun x => (hdu x).1) (fun x => (hdu x).2) hu2 hup


theorem direct_solvable_iff_two_pairings (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient) : (∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = f) ↔ pairing ρ f (curvedCosine ρ n).val = 0 ∧ pairing ρ f (curvedSine ρ n).val = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    exact mode_pairings ρ n u f hu
  · rintro ⟨hc,hs⟩
    exact weighted_direct_solution ρ n hn f hc hs
theorem direct_solvable_iff_raw_mode_periods (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient) : (∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = f) ↔ (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * (curvedCosine ρ n).val) (fromTrace p) = 0) ∧ (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * (curvedSine ρ n).val) (fromTrace p) = 0) := by
  rw [direct_solvable_iff_two_pairings ρ n hn f,
    trace_periods_iff_pairing ρ f (curvedCosine ρ n).val,
    trace_periods_iff_pairing ρ f (curvedSine ρ n).val]
theorem direct_solvable_iff_cochain_mode_periods (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient) : (∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = f) ↔ (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * (curvedCosine ρ n).val)).val = 0) ∧ (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * (curvedSine ρ n).val)).val = 0) := by
  rw [direct_solvable_iff_two_pairings ρ n hn f,
    cochain_periods_iff_pairing ρ f (curvedCosine ρ n).val,
    cochain_periods_iff_pairing ρ f (curvedSine ρ n).val]
end ComputationalHodge.ResonantPeriodsPrototype
#print axioms ComputationalHodge.ResonantPeriodsPrototype.direct_solvable_iff_raw_mode_periods
#print axioms ComputationalHodge.ResonantPeriodsPrototype.direct_solvable_iff_cochain_mode_periods
