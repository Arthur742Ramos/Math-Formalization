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
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Proof-complete shared generated source. All retained declarations and proofs
are copied verbatim from the ordered modular sources. No source pruning.
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

structure ContinuousGeometricStepSystem (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    extends GeometricStepSystem A Step where
  continuous_src : Continuous src
  continuous_tgt : Continuous tgt
  continuous_realize :
    Continuous (fun s => (realize s).toContinuousMap)

structure ScopedGeometricRewritePresentation
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
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
def period {S : GeometricStepSystem A E} {a b : A} :
    GeometricTrace S a b → Cochain E →ₗ[ℝ] ℝ
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
noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) :
    ScopedGeometricRewritePresentation S where
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

theorem winding_homotopic {p q : _root_.Path (0 : AddCircle (1 : ℝ)) 0}
    (h : _root_.Path.Homotopic p q) : winding p = winding q :=
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
theorem cut_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0} {c : ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hc : f c=g c) :
    LipschitzWith (K+L) (fun x => if x≤c then f x else g x) := by
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

theorem shift_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) :
    LipschitzWith K (fun x => c+f x) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub] using hf.dist_le_mul x y

theorem rawLift_lipschitz {a b : CircleHodge.Circle} (p : Trace a b) :
    ∃ K : ℝ≥0,LipschitzWith K (rawLift p) := by
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

theorem clamp_differentiable {x : ℝ} (h0 : x≠0) (h1 : x≠1) :
    DifferentiableAt ℝ clamp x := by
  rcases lt_or_gt_of_ne h0 with hx|hx
  · have heq : clamp=ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [clamp,min_eq_right (hy.le.trans zero_le_one),max_eq_left hy.le]
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq).differentiableAt
  · rcases lt_or_gt_of_ne h1 with hy|hy
    · have heq : clamp=ᶠ[𝓝 x] (fun t : ℝ => t) := by
        filter_upwards [eventually_gt_nhds hx,eventually_lt_nhds hy] with y hy0 hy1
        simp [clamp,min_eq_right hy1.le,max_eq_right hy0.le]
      exact ((hasDerivAt_id x).congr_of_eventuallyEq heq).differentiableAt
    · have heq : clamp=ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds hy] with y hy1
        simp [clamp,min_eq_left hy1.le]
      exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heq).differentiableAt

theorem rawLift_finite_corners {a b : CircleHodge.Circle} (p : Trace a b) :
    ∃ s : Set ℝ,s.Finite ∧ ∀ x ∉ s,DifferentiableAt ℝ (rawLift p) x := by
  classical
  induction p with
  | refl _ => exact ⟨∅,Set.finite_empty,fun _ _ => differentiableAt_const _⟩
  | single _ =>
    refine ⟨{0,1},by simp,fun x hx => clamp_differentiable ?_ ?_⟩
    · intro h;apply hx;simp [h]
    · intro h;apply hx;simp [h]
  | trans p q hp hq =>
    obtain ⟨s,hs,hp⟩ := hp
    obtain ⟨u,hu,hq⟩ := hq
    let v : Set ℝ := {1/2} ∪ ((fun t : ℝ => t/2) '' s ∪ (fun t : ℝ => (t+1)/2) '' u)
    refine ⟨v,(Set.finite_singleton _).union ((hs.image _).union (hu.image _)),?_⟩
    intro x hx
    have hhalf : x≠1/2 := fun h => hx (Or.inl (Set.mem_singleton_iff.mpr h))
    rcases lt_or_gt_of_ne hhalf with h|h
    · have hc : 2*x∉s := by
        intro hc
        apply hx
        exact Or.inr (Or.inl ⟨2*x,hc,by ring⟩)
      have hd := (hp (2*x) hc).hasDerivAt.comp x
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))
      have heq : rawLift (p.trans q)=ᶠ[𝓝 x] (fun t => rawLift p (2*t)) := by
        filter_upwards [eventually_lt_nhds h] with y hy
        simp only [rawLift,ite_eq_left hy.le]
      exact (hd.congr_of_eventuallyEq heq).differentiableAt
    · have hc : 2*x-1∉u := by
        intro hc
        apply hx
        exact Or.inr (Or.inr ⟨2*x-1,hc,by ring⟩)
      have hd := ((hasDerivAt_const x (rawLift p 1)).add
        ((hq (2*x-1) hc).hasDerivAt.comp x
          (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).sub_const 1)))
      have heq : rawLift (p.trans q)=ᶠ[𝓝 x] (fun t => rawLift p 1+rawLift q (2*t-1)) := by
        filter_upwards [eventually_gt_nhds h] with y hy
        simp only [rawLift,ite_eq_right (not_le.mpr hy)]
      exact (hd.congr_of_eventuallyEq heq).differentiableAt
  | symm p hp =>
    obtain ⟨s,hs,hp⟩ := hp
    refine ⟨(fun t : ℝ => 1-t) '' s,hs.image _,?_⟩
    intro x hx
    have hc : 1-x∉s := by
      intro hc
      exact hx ⟨1-x,hc,by ring⟩
    exact (((hp (1-x) hc).hasDerivAt.comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).sub_const _).differentiableAt

theorem rawLift_one_coe {a b : CircleHodge.Circle} (p : Trace a b) : ((rawLift p 1 : ℝ) : CircleHodge.Circle)=0 := by
  rw [rawLift_one]
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
  exact ⟨count p,by simp⟩

theorem rawLift_projects {a b : CircleHodge.Circle} (p : Trace a b) (t : unitInterval) :
    ((rawLift p (t : ℝ) : ℝ) : CircleHodge.Circle)+a=GeometricTrace.realize p t := by
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

theorem rawLift_outside {a b : CircleHodge.Circle} (p : Trace a b) :
    ∀ t : ℝ,(t≤0 → rawLift p t=0) ∧ (1≤t → rawLift p t=rawLift p 1) := by
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

theorem rawLift_clamp {a b : CircleHodge.Circle} (p : Trace a b) (t : ℝ) :
    rawLift p (Set.projIcc 0 1 zero_le_one t : ℝ)=rawLift p t := by
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

theorem rawLift_eq_cover (p : Trace 0 0) (t : unitInterval) :
    rawLift p (t : ℝ)=circleLift (GeometricTrace.realize p) t := by
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

theorem period_mean_count (α : Coefficient) {a b : CircleHodge.Circle} (p : Trace a b) :
    period p (meanCochain α)=mean α*(count p : ℝ) := by
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

theorem count_homotopic {a b : CircleHodge.Circle} (p q : Trace a b)
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) : count p=count q := by
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
theorem actual_lift_on_interval (L : ACLift) (t : unitInterval) :
    circleLift (projectedLoop L) t=L.val (t : ℝ) := by
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
theorem projected_fromTrace (p : Trace 0 0) :
    projectedLoop (fromTrace p)=GeometricTrace.realize p := by
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
theorem derivative_integral (L : ACLift) :
    ∫ t in (0 : ℝ)..1,deriv L.val t=L.val 1 := by
  simpa [L.property.2.1] using L.property.1.integral_deriv_eq_sub
theorem defect_integrable (L : ACLift) (h : FiniteEnergy L) :
    IntervalIntegrable (fun t => (deriv L.val t-L.val 1)^2) volume 0 1 := by
  convert (h.sub (L.property.1.intervalIntegrable_deriv.const_mul (2*L.val 1))).add
    (intervalIntegrable_const (c := (L.val 1)^2)) using 1
  ext t
  ring
theorem energy_splitting (L : ACLift) (h : FiniteEnergy L) :
    energy L=(L.val 1)^2+defect L := by
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
theorem minimum_implies_affine (L : ACLift) (h : FiniteEnergy L)
    (he : energy L=(L.val 1)^2) : ∀ t∈Icc (0 : ℝ) 1,L.val t=L.val 1*t := by
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
theorem energy_congr_on {L M : ACLift} (h : EqOn L.val M.val (Icc 0 1)) :
    energy L=energy M := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have ht' : t∈Ioo (0 : ℝ) 1 := by simpa [uIoo_of_lt zero_lt_one] using ht
  have he : L.val=ᶠ[nhds t] M.val := by
    filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with x hx
    exact h ⟨hx.1.le,hx.2.le⟩
  exact congrArg (fun x : ℝ => x^2) he.deriv_eq
theorem minimum_iff_affine (L : ACLift) (h : FiniteEnergy L) :
    energy L=(L.val 1)^2 ↔ EqOn L.val (affine L).val (Icc 0 1) := by
  constructor
  · exact minimum_implies_affine L h
  · intro he;rw [energy_congr_on he,affine_energy]
/-- Actual endpoint-fixed homotopy obtained by linear interpolation of the real lifts. -/
noncomputable def affineHomotopy (L : ACLift) :
    _root_.Path.Homotopy (projectedLoop L) (projectedLoop (affine L)) where
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
theorem affine_homotopic (L : ACLift) :
    _root_.Path.Homotopic (projectedLoop L) (projectedLoop (affine L)) := ⟨affineHomotopy L⟩
theorem class_minimum (L M : ACLift) (h : FiniteEnergy M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    energy (affine L)≤energy M := by
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
def paused : Trace 0 0 := .trans unitTrace (.refl 0)
theorem paused_endpoint : (fromTrace paused).val 1=1 := by
  change actualLift paused 1=1
  rw [actualLift_eq_rawLift,rawLift_one];norm_num [paused,unitTrace,count]
theorem paused_not_affine : ¬EqOn (fromTrace paused).val (affine (fromTrace paused)).val (Icc 0 1) := by
  intro h
  have hh := h (x := (1/2 : ℝ)) (by norm_num)
  change actualLift paused (1/2)=(fromTrace paused).val 1*(1/2) at hh
  rw [paused_endpoint,actualLift_eq_rawLift] at hh
  norm_num [paused,unitTrace,rawLift,clamp] at hh
theorem paused_energy_strict : 1<energy (fromTrace paused) := by
  have hl := energy_lower_bound (fromTrace paused) (fromTrace_finite paused)
  have hn : energy (fromTrace paused)≠1 := by
    intro he
    apply paused_not_affine
    apply (minimum_iff_affine _ (fromTrace_finite paused)).mp
    simpa [paused_endpoint] using he
  rw [paused_endpoint] at hl
  norm_num at hl
  exact lt_of_le_of_ne hl (Ne.symm hn)
theorem computational_minimum (p : Trace 0 0) :
    energy (affine (fromTrace p))=(period p unitCochain)^2 := by
  rw [affine_energy,period_unit_count]
  change (actualLift p 1)^2=(count p : ℝ)^2
  rw [actualLift_eq_rawLift,rawLift_one]
end ComputationalHodge.Dirichlet

namespace ComputationalHodge.UnitCircleGeometry
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.Dirichlet
open MeasureTheory Set Complex
open scoped NNReal Topology unitInterval ComplexConjugate
noncomputable def embed (x : CircleHodge.Circle) : ℂ := (AddCircle.toCircle x : ℂ)
theorem embed_zero : embed 0=1 := by simp [embed]
theorem embed_norm (x : CircleHodge.Circle) : ‖embed x‖=1 := (AddCircle.toCircle x).norm_coe
theorem embed_injective : Function.Injective embed := by
  intro x y h
  exact AddCircle.injective_toCircle (by norm_num : (1 : ℝ)≠0) (Subtype.ext h)
noncomputable def embedMap : C(CircleHodge.Circle,ℂ) :=
  ⟨embed,continuous_subtype_val.comp AddCircle.continuous_toCircle⟩
noncomputable def embeddedPath (L : ACLift) : _root_.Path (embed 0) (embed 0) :=
  (projectedLoop L).map embedMap.continuous
theorem embedded_base (L : ACLift) : embeddedPath L 0=1 ∧ embeddedPath L 1=1 := by
  simp only [Path.source,Path.target,embed_zero,and_self]
noncomputable def curve (L : ACLift) (t : ℝ) : ℂ :=
  embeddedPath L (Set.projIcc 0 1 zero_le_one t)
theorem curve_norm (L : ACLift) (t : ℝ) : ‖curve L t‖=1 := embed_norm _
theorem embedded_fromTrace (p : Trace 0 0) :
    embeddedPath (fromTrace p)=(GeometricTrace.realize p).map embedMap.continuous := by
  ext t
  change embed (projectedLoop (fromTrace p) t)=embed (GeometricTrace.realize p t)
  rw [projected_fromTrace]
theorem curve_eq_on (L : ACLift) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    curve L t=embed ((L.val t : ℝ) : CircleHodge.Circle) := by
  change embed ((L.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)=_
  rw [Set.projIcc_of_mem zero_le_one ht]
theorem embed_coe (x : ℝ) : embed (x : CircleHodge.Circle)=circleMap 0 1 (2*Real.pi*x) := by
  simp [embed,AddCircle.toCircle_apply_mk,Circle.coe_exp,circleMap]
theorem curve_deriv (L : ACLift) {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ L.val t) :
    deriv (curve L) t=curve L t*Complex.I*((2*Real.pi*deriv L.val t : ℝ) : ℂ) := by
  have he : curve L=ᶠ[nhds t] (fun x => circleMap 0 1 (2*Real.pi*L.val x)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    rw [curve_eq_on L ⟨hx.1.le,hx.2.le⟩,embed_coe]
  rw [he.deriv_eq]
  have h := (hasDerivAt_circleMap 0 1 (2*Real.pi*L.val t)).scomp t
    (hd.hasDerivAt.const_mul (2*Real.pi))
  rw [curve_eq_on L ⟨ht.1.le,ht.2.le⟩,embed_coe]
  simpa only [Function.comp_def,Complex.real_smul,mul_comm] using h.deriv
theorem derivative_ae (L : ACLift) :
    ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv (curve L) t=curve L t*Complex.I*((2*Real.pi*deriv L.val t : ℝ) : ℂ) := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1=ᵐ[volume] Ioc 0 1)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae L.property.1.ae_differentiableAt] with t ht hd
  exact curve_deriv L ht (hd (by simpa [uIcc_of_le zero_le_one] using ⟨ht.1.le,ht.2.le⟩))
/-- Actual real-linear angular covector. It is normalized on the unit-circle image. -/
noncomputable def angularForm (z : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun v := (conj z*v).im/(2*Real.pi)
  map_add' u v := by simp [mul_add,add_div]
  map_smul' r v := by simp [smul_eq_mul];ring
theorem angular_tangent (z : ℂ) (hz : ‖z‖=1) (a : ℝ) :
    angularForm z (z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))=a := by
  have hn : conj z*z=1 := by
    simpa only [hz,one_pow,Complex.ofReal_one] using Complex.conj_mul' z
  change (conj z*(z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))).im/(2*Real.pi)=a
  have he : conj z*(z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))=
      (conj z*z)*Complex.I*((2*Real.pi*a : ℝ) : ℂ) := by ring
  rw [he,hn,one_mul]
  simp [Complex.mul_im,Real.pi_ne_zero]
theorem angular_pullback_ae (L : ACLift) :
    (fun t => angularForm (curve L t) (deriv (curve L) t))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv L.val := by
  filter_upwards [derivative_ae L] with t ht
  rw [ht];exact angular_tangent _ (curve_norm L t) _
theorem angular_integrable (L : ACLift) :
    IntervalIntegrable (fun t => angularForm (curve L t) (deriv (curve L) t)) volume 0 1 := by
  apply L.property.1.intervalIntegrable_deriv.congr_ae
  simpa only [uIoc_of_le zero_le_one] using (angular_pullback_ae L).symm
noncomputable def angularIntegral (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,angularForm (curve L t) (deriv (curve L) t)
theorem angular_integral (L : ACLift) : angularIntegral L=L.val 1 := by
  unfold angularIntegral
  calc
    _ = ∫ t in (0 : ℝ)..1,deriv L.val t := intervalIntegral.integral_congr_ae_restrict (by
      simpa only [uIoc_of_le zero_le_one] using angular_pullback_ae L)
    _ = _ := derivative_integral L
theorem speed_squared_ae (L : ACLift) :
    (fun t => ‖deriv (curve L) t‖^2)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t => (2*Real.pi)^2*(deriv L.val t)^2) := by
  filter_upwards [derivative_ae L] with t ht
  rw [ht,norm_mul,norm_mul,curve_norm,Complex.norm_I,one_mul,one_mul,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
def AmbientFiniteEnergy (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => ‖deriv (curve L) t‖^2) volume 0 1
noncomputable def ambientEnergy (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,‖deriv (curve L) t‖^2
theorem finite_energy_iff (L : ACLift) : AmbientFiniteEnergy L ↔ FiniteEnergy L := by
  constructor
  · intro h
    have hs : IntervalIntegrable (fun t => (2*Real.pi)^2*(deriv L.val t)^2) volume 0 1 :=
      h.congr_ae (by simpa only [uIoc_of_le zero_le_one] using speed_squared_ae L)
    apply (hs.const_mul ((2*Real.pi)^2)⁻¹).congr
    intro t ht
    field_simp
  · intro h
    exact (h.const_mul ((2*Real.pi)^2)).congr_ae (by
      simpa only [uIoc_of_le zero_le_one] using (speed_squared_ae L).symm)
theorem ambient_energy (L : ACLift) : ambientEnergy L=(2*Real.pi)^2*energy L := by
  unfold ambientEnergy energy
  calc
    _ = ∫ t in (0 : ℝ)..1,(2*Real.pi)^2*(deriv L.val t)^2 :=
      intervalIntegral.integral_congr_ae_restrict (by
        simpa only [uIoc_of_le zero_le_one] using speed_squared_ae L)
    _ = _ := intervalIntegral.integral_const_mul _ _
theorem angular_computational (p : Trace 0 0) : angularIntegral (fromTrace p)=period p unitCochain := by
  rw [angular_integral,period_unit_count]
  change actualLift p 1=(count p : ℝ)
  rw [actualLift_eq_rawLift,rawLift_one]
theorem angular_harmonic (α : Coefficient) (p : Trace 0 0) :
    mean α*angularIntegral (fromTrace p)=period p (meanHarmonic α) := by
  rw [angular_computational,period_unit_count]
  exact (period_mean_count α p).symm
noncomputable def circlePath (L : ACLift) :
    _root_.Path (AddCircle.toCircle (0 : CircleHodge.Circle)) (AddCircle.toCircle (0 : CircleHodge.Circle)) :=
  (projectedLoop L).map AddCircle.continuous_toCircle
theorem circle_path_base (L : ACLift) : circlePath L 0=1 ∧ circlePath L 1=1 := by
  simp only [Path.source,Path.target,AddCircle.toCircle_zero,and_self]
theorem curve_from_circlePath (L : ACLift) (t : ℝ) :
    curve L t=(circlePath L (Set.projIcc 0 1 zero_le_one t) : ℂ) := rfl
theorem circle_homotopy (L : ACLift) :
    _root_.Path.Homotopic (circlePath L) (circlePath (affine L)) :=
  (affine_homotopic L).map ⟨AddCircle.toCircle,AddCircle.continuous_toCircle⟩
theorem curve_eq_iff (L M : ACLift) : curve L=curve M ↔ EqOn L.val M.val (Icc 0 1) := by
  constructor
  · intro h
    have hp : projectedLoop L=projectedLoop M := by
      ext t
      apply embed_injective
      have hh := congrFun h (t : ℝ)
      rwa [curve_eq_on L t.property,curve_eq_on M t.property] at hh
    intro t ht
    rw [← actual_lift_on_interval L ⟨t,ht⟩,← actual_lift_on_interval M ⟨t,ht⟩,hp]
  · intro h
    funext t
    have ht := (Set.projIcc 0 1 zero_le_one t).property
    change embed ((L.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)=
      embed ((M.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)
    rw [h ht]
theorem ambient_minimum_rigid (L : ACLift) (h : AmbientFiniteEnergy L) :
    ambientEnergy L=(2*Real.pi)^2*(L.val 1)^2 ↔ curve L=curve (affine L) := by
  rw [ambient_energy,mul_right_inj' (by positivity : (2*Real.pi)^2≠0),
    curve_eq_iff,minimum_iff_affine L ((finite_energy_iff L).mp h)]
theorem ambient_class_minimum (L M : ACLift) (h : AmbientFiniteEnergy M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    ambientEnergy (affine L)≤ambientEnergy M := by
  rw [ambient_energy,ambient_energy]
  exact mul_le_mul_of_nonneg_left (class_minimum L M ((finite_energy_iff M).mp h) hm) (sq_nonneg _)
theorem raw_finite_energy (p : Trace 0 0) : AmbientFiniteEnergy (fromTrace p) :=
  (finite_energy_iff _).mpr (fromTrace_finite p)
theorem computational_energy_minimum (p : Trace 0 0) :
    ambientEnergy (affine (fromTrace p))=(2*Real.pi)^2*(period p unitCochain)^2 := by
  rw [ambient_energy,computational_minimum]
theorem paused_strict : (2*Real.pi)^2<ambientEnergy (fromTrace paused) := by
  rw [ambient_energy]
  exact lt_mul_of_one_lt_right (by positivity : (0 : ℝ)<(2*Real.pi)^2) paused_energy_strict
end ComputationalHodge.UnitCircleGeometry
