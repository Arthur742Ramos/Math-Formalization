module
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-! Complete retained proofs and documented exact adaptations. -/
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
theorem cover_integrand_integrable (α : Coefficient) (L : ACLift) : IntervalIntegrable (fun t => cover α (L.val t)*deriv L.val t) volume 0 1 := by
  apply (primitive_comp_ac α L).intervalIntegrable_deriv.congr_ae
  exact (ae_restrict_mem measurableSet_uIoc).and (ae_restrict_of_ae (chain_rule_ae α L)) |>.mono
    (fun t ht => ht.2 (uIoc_subset_uIcc ht.1))
theorem lineIntegral_eq_cover (α : Coefficient) (L : ACLift) : lineIntegral α L=∫ t in (0 : ℝ)..1,cover α (L.val t)*deriv L.val t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have h : t∈Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  exact congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t) (Set.projIcc_of_mem zero_le_one h)
theorem line_integrand_integrable (α : Coefficient) (L : ACLift) : IntervalIntegrable (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t) volume 0 1 := by
  apply (cover_integrand_integrable α L).congr
  intro t ht
  have h : t∈Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)
  exact (congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t) (Set.projIcc_of_mem zero_le_one h)).symm
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
theorem lineIntegral_unit (α : Coefficient) : lineIntegral α (fromTrace unitTrace)=mean α := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift unitTrace 1=mean α
  rw [actualLift_eq_rawLift,rawLift_one]
  simp [unitTrace,count]
end ComputationalHodge.ACLifts
namespace ComputationalHodge.CircleHodge
open Set
/-- A genuine real primitive with its mean term removed. -/
noncomputable def realPotential (α : Coefficient) (x : ℝ) : ℝ :=
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
/-- The primitive descends to an actual continuous function on the circle. -/
noncomputable def potential (α : Coefficient) : Coefficient where
  toFun := (realPotential_periodic α).lift
  continuous_toFun := (realPotential_contDiff α).continuous.quotient_liftOn' _
theorem potential_contDiff (α : Coefficient) : ContDiff ℝ 1 (cover (potential α)) :=
  realPotential_contDiff α
theorem potential_deriv (α : Coefficient) (x : ℝ) : deriv (cover (potential α)) x=cover α x-mean α :=
  (realPotential_hasDerivAt α x).deriv
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
theorem derivative_cover (f : Coefficient) (hf : ContDiff ℝ 1 (cover f)) (x : ℝ) : cover (derivativeCoefficient f hf) x=deriv (cover f) x := rfl
noncomputable def gradient (u : C2Coefficient) : Coefficient := derivativeCoefficient u.val (c2_c1 u)
theorem gradient_cover (u : C2Coefficient) (x : ℝ) : cover (gradient u) x=deriv (cover u.val) x := rfl
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
theorem weightedMean_sub (ρ : RegularDensity) (f g : Coefficient) : weightedMean ρ (f-g)=weightedMean ρ f-weightedMean ρ g := by
  unfold weightedMean
  rw [mul_sub,mean_sub]
theorem weightedMean_constant (ρ : RegularDensity) (c : ℝ) : weightedMean ρ (constant c)=c*mean ρ.val.val := by
  have he : ρ.val.val*constant c=c•ρ.val.val := by ext q;change _*c=c*_;ring
  rw [weightedMean,he,mean_smul]
noncomputable def constantC2 (c : ℝ) : C2Coefficient := ⟨constant c,by change ContDiff ℝ 2 (fun _ : ℝ => c);exact contDiff_const⟩
theorem gradient_sub (u v : C2Coefficient) : gradient (u-v)=gradient u-gradient v := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  exact deriv_sub ((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x) ((contDiff_one_iff_deriv.mp (c2_c1 v)).1 x)
theorem flux_sub (ρ : RegularDensity) (u v : C2Coefficient) : flux ρ (u-v)=flux ρ u-flux ρ v := by
  ext q
  change gradient (u-v) q/ρ.val.val q=gradient u q/ρ.val.val q-gradient v q/ρ.val.val q
  rw [gradient_sub]
  change (gradient u q-gradient v q)/ρ.val.val q=_
  ring
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
  have hf : flux ρ u=0 := by
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    change deriv (cover u.val) x/cover ρ.val.val x=0
    rw [hu]
    change deriv (fun _ : ℝ => c) x/cover ρ.val.val x=0
    rw [deriv_const,zero_div]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ u)) x)/cover ρ.val.val x=0
  rw [hf]
  change -(deriv (fun _ : ℝ => 0) x)/cover ρ.val.val x=0
  rw [deriv_const,neg_zero,zero_div]
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
    have hd (x : ℝ) : deriv (cover u.val) x=0 := by
      have h:=congrArg (fun f : Coefficient => cover f x) hg
      rw [h0,zero_smul] at h
      change deriv (cover u.val) x=0 at h
      exact h
    refine ⟨cover u.val 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero (contDiff_one_iff_deriv.mp (c2_c1 u)).1 hd x 0
  · rintro ⟨c,hc⟩;exact laplacian_of_constant ρ u c hc
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
/-- Constructed normalized Green solution to the forcing with its weighted constant projection removed. -/
noncomputable def green (ρ : RegularDensity) (f : Coefficient) : C2Coefficient :=
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
  have hm:=congrArg (weightedMean ρ) hc
  rw [weightedMean_sub,hu,hv,weightedMean_constant,sub_self] at hm
  have h0 : c=0 := (mul_eq_zero.mp hm.symm).resolve_right (ne_of_gt (mean_pos ρ.val))
  apply Subtype.ext
  apply sub_eq_zero.mp
  rw [hc,h0]
  rfl
theorem pairing_symmetry (ρ : RegularDensity) (u v : C2Coefficient) : (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)= ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover u.val x*cover (laplacian ρ v) x := by
  rw [green_identity]
  calc
    _ = ∫ x in (0 : ℝ)..1,cover (gradient v) x*cover (gradient u) x/cover ρ.val.val x :=
      intervalIntegral.integral_congr (fun _ _ => by ring)
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ v) x*cover u.val x := (green_identity ρ v u).symm
    _ = _ := intervalIntegral.integral_congr (fun _ _ => by ring)
theorem green_laplacian_eq_normalize (ρ : RegularDensity) (u : C2Coefficient) : green ρ (laplacian ρ u)=normalize ρ u := by
  apply normalized_unique ρ
  · rw [green_solves_projected,project_eq_self ρ _ (weightedMean_laplacian ρ u),normalize_laplacian]
  · exact green_mean_zero _ _
  · exact normalize_mean_zero _ _
noncomputable def cosine : Coefficient where
  toFun q := (AddCircle.toCircle q : ℂ).re
  continuous_toFun := by fun_prop
theorem cosine_cover (x : ℝ) : cover cosine x=Real.cos (2*Real.pi*x) := by
  change (AddCircle.toCircle (x : CircleHodge.Circle) : ℂ).re=_
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  norm_num [Complex.exp_re]
noncomputable def cosineC2 : C2Coefficient := ⟨cosine,by
  have he : cover cosine=fun x => Real.cos (2*Real.pi*x) := funext cosine_cover
  change ContDiff ℝ 2 (cover cosine)
  rw [he]
  fun_prop⟩
theorem cosine_zero : cosine 0=1 := by norm_num [cosine]
theorem cosine_half : cosine ((1/2 : ℝ) : CircleHodge.Circle)= -1 := (cosine_cover (1/2)).trans (by convert Real.cos_pi using 1;congr 1;ring)
theorem cosine_nonconstant : ¬∃ c : ℝ,cosine=constant c := by
  rintro ⟨c,h⟩
  have he:=congrArg (fun f : Coefficient => f 0-f ((1/2 : ℝ) : CircleHodge.Circle)) h
  norm_num [cosine_zero,cosine_half,constant] at he
end ComputationalHodge.Poisson
namespace ComputationalHodge.GreenOperator
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
theorem norm_of_positive {x : ℝ} (hx : 0<x) : ‖x‖=x := (Real.norm_eq_abs x).trans (abs_of_pos hx)
theorem weightedMean_add (ρ : RegularDensity) (f g : Coefficient) : weightedMean ρ (f+g)=weightedMean ρ f+weightedMean ρ g := by
  unfold weightedMean
  rw [mul_add]
  exact intervalIntegral.integral_add ((cover_continuous (ρ.val.val*f)).intervalIntegrable 0 1)
    ((cover_continuous (ρ.val.val*g)).intervalIntegrable 0 1)
theorem weightedMean_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) : weightedMean ρ (c•f)=c*weightedMean ρ f := by
  have h : ρ.val.val*(c•f)=c•(ρ.val.val*f) := by ext q;change _*(c*_) = c*(_*_);ring
  rw [weightedMean,h,mean_smul]
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
/-- Actual continuous weighted-mean functional, bounded using the positive density integral. -/
noncomputable def meanFunctional (ρ : RegularDensity) : Coefficient →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    {toFun:=weightedMean ρ,map_add':=weightedMean_add ρ,map_smul':=fun c f => weightedMean_smul ρ c f}
    (mean ρ.val.val) (weightedMean_bound ρ)
/-- Closed subspace of continuous forcing with vanishing actual computational obstruction. -/
noncomputable def compatibleSpace (ρ : RegularDensity) : Submodule ℝ Coefficient := (meanFunctional ρ).ker
abbrev Compatible (ρ : RegularDensity) := ↥(compatibleSpace ρ)
theorem compatible_iff (ρ : RegularDensity) (f : Coefficient) : f∈compatibleSpace ρ ↔ weightedMean ρ f=0 := Iff.rfl
theorem compatible_closed (ρ : RegularDensity) : IsClosed (compatibleSpace ρ : Set Coefficient) :=
  (meanFunctional ρ).isClosed_ker
instance compatible_complete (ρ : RegularDensity) : CompleteSpace (Compatible ρ) :=
  (compatible_closed ρ).completeSpace_coe
theorem compatible_iff_raw (ρ : RegularDensity) (f : Coefficient) : f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  ⟨fun h p => by rw [lineIntegral_eq_mean,show mean (ρ.val.val*f)=0 from h,zero_mul],
   fun h => by change mean (ρ.val.val*f)=0;simpa only [lineIntegral_unit] using h unitTrace⟩
theorem compatible_iff_periods (ρ : RegularDensity) (f : Coefficient) : f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := by
  rw [compatible_iff_raw];simp only [lineIntegral_fromTrace_harmonic]
/-- A quantitative actual primitive estimate; the bound is proved, not assumed for Green. -/
theorem potential_weight_bound (ρ : RegularDensity) (f : Coefficient) (hf : mean f=0) (C : ℝ) (hC : 0≤C) (h : ∀ q,‖f q‖≤C*ρ.val.val q) : ‖potential f‖≤C*mean ρ.val.val := by
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
/-- A bounded linear endomorphism of the actual closed C0 forcing subspace, with a C2 image. -/
noncomputable def greenMap (ρ : RegularDensity) : Compatible ρ →L[ℝ] Compatible ρ :=
  LinearMap.mkContinuous
    {toFun:=fun f => ⟨(solution ρ f).val,solution_mean_zero ρ f⟩,
     map_add':=fun f g => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_add ρ f g)),
     map_smul':=fun c f => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_smul ρ c f))}
    (4*(mean ρ.val.val)^2) (fun f => green_bound ρ f.val f.property)
theorem greenMap_apply (ρ : RegularDensity) (f : Compatible ρ) : (greenMap ρ f).val=(green ρ f.val).val := rfl
theorem greenMap_regular (ρ : RegularDensity) (f : Compatible ρ) : ContDiff ℝ 2 (cover (greenMap ρ f).val) :=
  (solution ρ f).property
theorem greenMap_right_inverse (ρ : RegularDensity) (f : Compatible ρ) : laplacian ρ ⟨(greenMap ρ f).val,greenMap_regular ρ f⟩=f.val := solution_solves ρ f
theorem greenMap_left_inverse (ρ : RegularDensity) (u : C2Coefficient) : (greenMap ρ ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩).val=(normalize ρ u).val :=
  congrArg Subtype.val (green_laplacian_eq_normalize ρ u)
theorem greenMap_bound (ρ : RegularDensity) (f : Compatible ρ) : ‖greenMap ρ f‖≤4*(mean ρ.val.val)^2*‖f‖ := green_bound ρ f.val f.property
theorem greenMap_injective (ρ : RegularDensity) : Function.Injective (greenMap ρ) :=
  fun f g h => Subtype.ext ((solution_solves ρ f).symm.trans
    ((congrArg (laplacian ρ) (show solution ρ f=solution ρ g from Subtype.ext (congrArg (fun u : Compatible ρ => u.val) h))).trans (solution_solves ρ g)))
theorem greenMap_stability (ρ : RegularDensity) (f g : Compatible ρ) : ‖greenMap ρ f-greenMap ρ g‖≤4*(mean ρ.val.val)^2*‖f-g‖ := by
  rw [← map_sub]
  exact green_bound ρ (f-g).val (f-g).property
theorem gradient_constant (c : ℝ) : gradient (constantC2 c)=0 := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  exact deriv_const x c
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
theorem greenMap_flux_bound (ρ : RegularDensity) (f : Compatible ρ) : ‖flux ρ (solution ρ f)‖≤2*mean ρ.val.val*‖f‖ := by
  have hm := (mean_pos ρ.val).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  change ‖gradient (solution ρ f) q/ρ.val.val q‖≤_
  rw [norm_div,norm_of_positive (ρ.val.property q),solution_gradient]
  exact (div_le_iff₀ (ρ.val.property q)).mpr (velocity_point_bound ρ f.val f.property q)
theorem greenMap_gradient_stability (ρ : RegularDensity) (f g : Compatible ρ) : ‖gradient (solution ρ f)-gradient (solution ρ g)‖≤2*mean ρ.val.val*‖ρ.val.val‖*‖f-g‖ := by
  have he : solution ρ (f-g)=solution ρ f-solution ρ g := Subtype.ext (congrArg (fun u : Compatible ρ => u.val) (map_sub (greenMap ρ) f g))
  simpa only [he,gradient_sub] using greenMap_gradient_bound ρ (f-g)
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/
noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
theorem greenMap_pairing_symmetry (ρ : RegularDensity) (f g : Compatible ρ) : pairing ρ f.val (greenMap ρ g).val=pairing ρ g.val (greenMap ρ f).val := by
  change (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f.val x*cover (solution ρ g).val x)=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover g.val x*cover (solution ρ f).val x
  calc
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (solution ρ f).val x*cover g.val x := by
      simpa only [solution_solves] using pairing_symmetry ρ (solution ρ f) (solution ρ g)
    _ = _ := intervalIntegral.integral_congr (fun x _ => by ring)
theorem solution_gradient_nonzero (ρ : RegularDensity) (f : Compatible ρ) (hf : f≠0) : ∃ q,gradient (solution ρ f) q≠0 := by
  by_contra h
  have hg : gradient (solution ρ f)=0 := by ext q;exact not_ne_iff.mp (not_exists.mp h q)
  have hc : ∃ c : ℝ,(solution ρ f).val=constant c := by
    refine ⟨cover (solution ρ f).val 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero ((contDiff_one_iff_deriv.mp (c2_c1 (solution ρ f))).1)
      (fun t => by change gradient (solution ρ f) (t : CircleHodge.Circle)=0;rw [hg];rfl) x 0
  obtain ⟨c,hc⟩:=hc
  exact hf (Subtype.ext ((solution_solves ρ f).symm.trans (laplacian_of_constant ρ _ c hc)))
theorem greenMap_pairing_positive (ρ : RegularDensity) (f : Compatible ρ) (hf : f≠0) : 0<pairing ρ f.val (greenMap ρ f).val := by
  obtain ⟨q,hq⟩:=solution_gradient_nonzero ρ f hf
  let e : Coefficient := gradient (solution ρ f)*flux ρ (solution ρ f)
  have he (t : CircleHodge.Circle) : e t=gradient (solution ρ f) t*gradient (solution ρ f) t/ρ.val.val t := by
    change gradient (solution ρ f) t*(gradient (solution ρ f) t/ρ.val.val t)=_;ring
  have hp : 0<mean e := by
    rw [mean_circle]
    apply integral_pos_of_integrable_nonneg_nonzero e.continuous (continuous_integrable e.continuous)
      (fun t => by rw [he];exact div_nonneg (mul_self_nonneg _) (ρ.val.property t).le)
    rw [he]
    exact ne_of_gt (div_pos (mul_self_pos.mpr hq) (ρ.val.property q))
  have hi:=green_identity ρ (solution ρ f) (solution ρ f)
  rw [solution_solves] at hi
  change 0<(∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f.val x*cover (solution ρ f).val x)
  rw [hi]
  have heI : mean e=(∫ x in (0 : ℝ)..1,cover (gradient (solution ρ f)) x*cover (gradient (solution ρ f)) x/cover ρ.val.val x) :=
    intervalIntegral.integral_congr (fun x _ => he (x : CircleHodge.Circle))
  exact heI ▸ hp
theorem greenMap_range_iff (ρ : RegularDensity) (u : Compatible ρ) : (∃ f,greenMap ρ f=u) ↔ ContDiff ℝ 2 (cover u.val) := by
  constructor
  · rintro ⟨f,rfl⟩;exact greenMap_regular ρ f
  · intro hu
    let v : C2Coefficient := ⟨u.val,hu⟩
    refine ⟨⟨laplacian ρ v,weightedMean_laplacian ρ v⟩,Subtype.ext ?_⟩
    rw [greenMap_left_inverse]
    have hm : weightedMean ρ u.val=0 := u.property
    change u.val-constant (weightedMean ρ u.val/mean ρ.val.val)=u.val
    rw [hm,zero_div]
    ext q;exact sub_zero _
/-- A concrete nonzero compatible forcing for every admitted density; not a vacuous zero space. -/
noncomputable def exampleForcing (ρ : RegularDensity) : Compatible ρ :=
  ⟨laplacian ρ cosineC2,weightedMean_laplacian ρ cosineC2⟩
theorem exampleForcing_nonzero (ρ : RegularDensity) : exampleForcing ρ≠0 :=
  fun h => cosine_nonconstant ((kernel_iff_constant ρ cosineC2).mp (congrArg (fun f : Compatible ρ => f.val) h))
theorem example_pairing_positive (ρ : RegularDensity) : 0<pairing ρ (exampleForcing ρ).val (greenMap ρ (exampleForcing ρ)).val :=
  greenMap_pairing_positive ρ (exampleForcing ρ) (exampleForcing_nonzero ρ)
end ComputationalHodge.GreenOperator
