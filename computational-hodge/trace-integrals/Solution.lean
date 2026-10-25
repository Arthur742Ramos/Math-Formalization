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
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

theorem period_d0 {S : GeometricStepSystem A E} (f : A → ℝ)
    {a b : A} (p : GeometricTrace S a b) : period p (d0 S f) = f b - f a := by
  induction p with
  | refl a => simp [period]
  | single e => rfl
  | trans p q hp hq =>
    change period p (d0 S f) + period q (d0 S f) = _
    rw [hp, hq]
    ring
  | symm p hp =>
    change -period p (d0 S f) = _
    rw [hp]
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

theorem d1_d0 (P : ScopedGeometricRewritePresentation S) (f : A → ℝ) :
    d1 P (d0 S.toGeometricStepSystem f) = 0 := by
  funext c
  change period c.left (d0 S.toGeometricStepSystem f) -
    period c.right (d0 S.toGeometricStepSystem f) = 0
  rw [period_d0, period_d0, sub_self]

theorem exact_le_closed (P : ScopedGeometricRewritePresentation S) : Exact S ≤ Closed P := by
  rintro _ ⟨f, rfl⟩
  exact d1_d0 P f

theorem closed_rule (P : ScopedGeometricRewritePresentation S) (ω : Closed P)
    {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b} (h : P.rule p q) :
    period p ω = period q ω := by
  have h' := congrFun ω.property (Cell.mk a b p q h)
  exact sub_eq_zero.mp h'

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

/-- The ambient fundamental-groupoid class of an actual realized computational trace. -/
noncomputable def traceClass {x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    _root_.Path.Homotopic.Quotient x y :=
  _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p)

theorem traceClass_refl (x : A) : traceClass (S := S) (.refl x) =
    _root_.Path.Homotopic.Quotient.refl x := rfl

theorem traceClass_trans {x y z : A} (p : GeometricTrace S.toGeometricStepSystem x y)
    (q : GeometricTrace S.toGeometricStepSystem y z) :
    traceClass (.trans p q) = (traceClass p).trans (traceClass q) :=
  _root_.Path.Homotopic.Quotient.mk_trans _ _

theorem traceClass_symm {x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    traceClass (.symm p) = (traceClass p).symm :=
  _root_.Path.Homotopic.Quotient.mk_symm _

/-- Actual image subgroup in the ambient fundamental group, not a newly stipulated quotient. -/
noncomputable def representedGroup (S : ContinuousGeometricStepSystem A E) (a : A) :
    Subgroup (FundamentalGroup A a) where
  carrier g := ∃ p : GeometricTrace S.toGeometricStepSystem a a, traceClass p = g
  one_mem' := ⟨.refl a,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨.trans q p,traceClass_trans q p⟩
  inv_mem' := by
    rintro _ ⟨p,rfl⟩
    exact ⟨.symm p,traceClass_symm p⟩

noncomputable def representedLoop {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) :
    representedGroup S a := ⟨traceClass p,p,rfl⟩

theorem representedLoop_refl (a : A) : representedLoop (S := S) (.refl a) = 1 := rfl

theorem representedLoop_trans {a : A} (p q : GeometricTrace S.toGeometricStepSystem a a) :
    representedLoop (.trans p q) = representedLoop q * representedLoop p :=
  Subtype.ext (traceClass_trans p q)

theorem representedLoop_symm {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) :
    representedLoop (.symm p) = (representedLoop p)⁻¹ := Subtype.ext (traceClass_symm p)

/-- Only computational endpoints, plus the root, need be connected by traces. -/
def Active (S : ContinuousGeometricStepSystem A E) (a x : A) : Prop :=
  x = a ∨ ∃ e : E, S.src e = x ∨ S.tgt e = x

structure Rooting (S : ContinuousGeometricStepSystem A E) (a : A) where
  trace : (x : A) → Active S a x → GeometricTrace S.toGeometricStepSystem a x
  at_root : trace a (Or.inl rfl) = .refl a

theorem active_endpoints {a x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    Active S a x ↔ Active S a y := by
  induction p with
  | refl => rfl
  | single e => exact iff_of_true (Or.inr ⟨e,Or.inl rfl⟩) (Or.inr ⟨e,Or.inr rfl⟩)
  | trans p q hp hq => exact hp.trans hq
  | symm p hp => exact hp.symm

variable [Fintype E]

theorem inactive_period_zero {a x y : A} (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : ¬ Active S a x) (ω : Cochain E) : period p ω = 0 := by
  induction p with
  | refl => rfl
  | single e => exact (hx (Or.inr ⟨e,Or.inl rfl⟩)).elim
  | trans p q hp hq =>
    change period p ω + period q ω = 0
    rw [hp hx,hq (fun hy => hx ((active_endpoints p).mpr hy)),add_zero]
  | symm p hp =>
    change -period p ω = 0
    rw [hp (fun hy => hx ((active_endpoints p).mp hy)),neg_zero]

/-- Complete geometric relations are actual endpoint-fixed path homotopies. -/
noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) :
    ScopedGeometricRewritePresentation S where
  rule p q := _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule h := h

theorem closed_period_homotopic (ω : Closed (geometricPresentation S)) {x y : A}
    (p q : GeometricTrace S.toGeometricStepSystem x y)
    (h : traceClass p = traceClass q) : period p ω = period q ω :=
  closed_rule (geometricPresentation S) ω (_root_.Path.Homotopic.Quotient.eq.mp h)

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

theorem winding_refl : winding (_root_.Path.refl (0 : AddCircle (1 : ℝ))) = 0 := by
  exact congrArg (fun f : C(unitInterval,ℝ) => f 1)
    (circleCover.liftPath_const (e := (0 : ℝ)) (x := (0 : AddCircle (1 : ℝ))) (by simp))

theorem circleLift_translate (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) (u : ℝ)
    (hu : (u : AddCircle (1 : ℝ)) = 0) :
    (⟨fun t => u + circleLift p t,continuous_const.add (circleLift p).continuous⟩ :
      C(unitInterval,ℝ)) = circleCover.liftPath p.toContinuousMap u (by simp [hu]) := by
  apply (circleCover.eq_liftPath_iff' _).mpr
  constructor
  · funext t
    change ((u + circleLift p t : ℝ) : AddCircle (1 : ℝ)) = p t
    rw [AddCircle.coe_add,hu,zero_add]
    exact congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) t
  · change u + circleCover.liftPath p.toContinuousMap 0 _ 0 = u
    rw [circleCover.liftPath_zero,add_zero]

theorem winding_trans (p q : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    winding (p.trans q) = winding p + winding q := by
  have hu : ((circleLift p 1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) 1).trans p.target
  have ht := congrArg (fun f : C(unitInterval,ℝ) => f 1)
    (circleCover.liftPath_trans (e := (0 : ℝ)) (by simp) p q)
  simp only [ContinuousMap.coe_coe,_root_.Path.trans_apply] at ht
  norm_num at ht
  change winding (p.trans q) = circleCover.liftPath q.toContinuousMap (circleLift p 1) _ 1 at ht
  rw [ht,← circleLift_translate q (circleLift p 1) hu]
  rfl

/-- A real character of the actual ambient fundamental group, constructed by lifting. -/
noncomputable def windingCharacter : FundamentalGroup (AddCircle (1 : ℝ)) 0 →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (g.lift winding (fun _ _ h => winding_homotopic h))
  map_one' := winding_refl
  map_mul' g h := by
    induction g using Quotient.inductionOn with | _ p =>
    induction h using Quotient.inductionOn with | _ q =>
    exact (winding_trans q p).trans (add_comm _ _)

def onceAround : _root_.Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := by simp
  target' := by simp

theorem winding_onceAround : winding onceAround = 1 := by
  have h : (⟨fun t : unitInterval => (t : ℝ),continuous_subtype_val⟩ : C(unitInterval,ℝ)) =
      circleLift onceAround := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,rfl⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f 1) h).symm

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

abbrev Trace (a b : Circle) := GeometricTrace circleSystem.toGeometricStepSystem a b

def count {a b : Circle} : Trace a b → ℤ
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => count p+count q
  | .symm p => -count p

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

/-- A finite piecewise-affine construction from the actual trace syntax.
Equality with the actual covering lift is proved separately. -/
noncomputable def rawLift {a b : Circle} : Trace a b → ℝ → ℝ
  | .refl _ => fun _ => 0
  | .single _ => clamp
  | .trans p q => fun t => if t≤1/2 then rawLift p (2*t)
      else rawLift p 1+rawLift q (2*t-1)
  | .symm p => fun t => rawLift p (1-t)-rawLift p 1

theorem trace_endpoints {a b : Circle} (p : Trace a b) : a=b := by
  induction p with
  | refl _ => rfl
  | single _ => rfl
  | trans p q hp hq => exact hp.trans hq
  | symm p hp => exact hp.symm

theorem rawLift_zero {a b : Circle} (p : Trace a b) : rawLift p 0=0 := by
  induction p with
  | refl _ => rfl
  | single _ => norm_num [rawLift,clamp]
  | trans p q hp hq => norm_num [rawLift,hp]
  | symm p hp => simp [rawLift]

theorem rawLift_one {a b : Circle} (p : Trace a b) : rawLift p 1=(count p : ℝ) := by
  induction p with
  | refl _ => norm_num [rawLift,count]
  | single _ => norm_num [rawLift,clamp,count]
  | trans p q hp hq => norm_num [rawLift,count,hp,hq]
  | symm p hp => simp [rawLift,count,rawLift_zero,hp]

theorem rawLift_continuous {a b : Circle} (p : Trace a b) : Continuous (rawLift p) := by
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

theorem rawLift_lipschitz {a b : Circle} (p : Trace a b) :
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

theorem rawLift_finite_corners {a b : Circle} (p : Trace a b) :
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

theorem rawLift_one_coe {a b : Circle} (p : Trace a b) : ((rawLift p 1 : ℝ) : Circle)=0 := by
  rw [rawLift_one]
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
  exact ⟨count p,by simp⟩

theorem rawLift_projects {a b : Circle} (p : Trace a b) (t : unitInterval) :
    ((rawLift p (t : ℝ) : ℝ) : Circle)+a=GeometricTrace.realize p t := by
  induction p generalizing t with
  | refl a => simp [rawLift,GeometricTrace.realize]
  | single e =>
    change ((clamp (t : ℝ) : ℝ) : Circle)+0=((t : ℝ) : Circle)
    simp [clamp,min_eq_right t.2.2,max_eq_right t.2.1]
  | trans p q hp hq =>
    rw [GeometricTrace.realize,_root_.Path.trans_apply]
    by_cases h : (t : ℝ)≤1/2
    · rw [dite_eq_left h]
      change ((if (t : ℝ)≤1/2 then rawLift p (2*t) else rawLift p 1+rawLift q (2*t-1) : ℝ) : Circle)+_= _
      rw [ite_eq_left h]
      exact hp ⟨2*t,⟨by linarith [t.2.1],by linarith⟩⟩
    · rw [dite_eq_right h]
      change ((if (t : ℝ)≤1/2 then rawLift p (2*t) else rawLift p 1+rawLift q (2*t-1) : ℝ) : Circle)+_= _
      rw [ite_eq_right h,AddCircle.coe_add,rawLift_one_coe,zero_add]
      conv_lhs => rhs; rw [trace_endpoints p]
      exact hq ⟨2*t-1,⟨by linarith [not_le.mp h],by linarith [t.2.2]⟩⟩
  | symm p hp =>
    change ((rawLift p (1-(t : ℝ))-rawLift p 1 : ℝ) : Circle)+_=
      GeometricTrace.realize p (σ t)
    rw [AddCircle.coe_sub,rawLift_one_coe,sub_zero]
    conv_lhs => rhs; rw [←trace_endpoints p]
    exact hp (σ t)

theorem rawLift_outside {a b : Circle} (p : Trace a b) :
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

theorem rawLift_clamp {a b : Circle} (p : Trace a b) (t : ℝ) :
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
open MeasureTheory Set
open scoped NNReal Topology

/-- Ordinary integration on the actual realized path and its actual covering lift. -/
noncomputable def rawIntegral (α : Coefficient) (p : Trace 0 0) : ℝ :=
  ∫ t in (0 : ℝ)..1,α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
    deriv (actualLift p) t

theorem actual_coefficient (α : Coefficient) (p : Trace 0 0) (t : ℝ) :
    α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))=cover α (actualLift p t) := by
  apply congrArg α
  exact (congrFun (circleCover.liftPath_lifts
    (GeometricTrace.realize p).toContinuousMap 0 (by simp))
    (Set.projIcc 0 1 zero_le_one t)).symm

theorem actualLift_lipschitz (p : Trace 0 0) : ∃ K : ℝ≥0,LipschitzWith K (actualLift p) := by
  rw [actualLift_eq_rawLift]
  exact rawLift_lipschitz p

theorem actualLift_finite_corners (p : Trace 0 0) :
    ∃ s : Set ℝ,s.Finite ∧ ∀ x ∉ s,DifferentiableAt ℝ (actualLift p) x := by
  rw [actualLift_eq_rawLift]
  exact rawLift_finite_corners p

theorem cover_integrand_integrable (α : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable (fun t => cover α (actualLift p t)*deriv (actualLift p) t) volume 0 1 := by
  obtain ⟨K,hK⟩ := actualLift_lipschitz p
  obtain ⟨C,hC⟩ := (isCompact_range α.continuous).isBounded.exists_norm_le
  have hb (t : ℝ) : ‖cover α (actualLift p t)*deriv (actualLift p) t‖≤C*(K : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul (hC _ ⟨(actualLift p t : Circle),rfl⟩)
      (norm_deriv_le_of_lipschitz hK) (norm_nonneg _) (by
        exact (norm_nonneg (α 0)).trans (hC _ ⟨0,rfl⟩))
  have hm : AEStronglyMeasurable
      (fun t => cover α (actualLift p t)*deriv (actualLift p) t) (volume.restrict (Icc 0 1)) :=
    (((cover_continuous α).comp hK.continuous).aestronglyMeasurable).mul
      (aestronglyMeasurable_deriv (actualLift p) _)
  have hi : IntegrableOn (fun t => cover α (actualLift p t)*deriv (actualLift p) t)
      (Icc 0 1) volume :=
    IntegrableOn.of_bound (by simp) hm (C*(K : ℝ)) (Filter.Eventually.of_forall hb)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    (hi.mono_set Ioc_subset_Icc_self)

theorem raw_integrand_integrable (α : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable
      (fun t => α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
        deriv (actualLift p) t) volume 0 1 := by
  simpa only [actual_coefficient] using cover_integrand_integrable α p

theorem rawIntegral_eq_cover (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=∫ t in (0 : ℝ)..1,cover α (actualLift p t)*deriv (actualLift p) t := by
  simp only [rawIntegral,actual_coefficient]

theorem rawIntegral_eq_endpoint (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=∫ x in (0 : ℝ)..(count p : ℝ),cover α x := by
  let A : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u,cover α x
  have ha (x : ℝ) : HasDerivAt A (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  obtain ⟨K,hK⟩ := actualLift_lipschitz p
  obtain ⟨s,hs,hd⟩ := actualLift_finite_corners p
  have hA : Continuous A := (show Differentiable ℝ A from fun x => (ha x).differentiableAt).continuous
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => A (actualLift p t))
    (fun t => cover α (actualLift p t)*deriv (actualLift p) t)
    zero_le_one hs.countable (hA.comp hK.continuous).continuousOn
    (fun x hx => (ha (actualLift p x)).comp x ((hd x hx.2).hasDerivAt))
    (cover_integrand_integrable α p)
  rw [rawIntegral_eq_cover]
  simpa [A,actualLift_eq_rawLift,rawLift_zero,rawLift_one] using h

theorem rawIntegral_eq_mean_count (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=mean α*(count p : ℝ) := by
  rw [rawIntegral_eq_endpoint]
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq (count p) 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simpa [mean,mul_comm] using h

theorem winding_realize_count (p : Trace 0 0) : winding (GeometricTrace.realize p)=(count p : ℝ) := by
  exact (rawLift_eq_cover p 1).symm.trans (rawLift_one p)

end ComputationalHodge.TraceIntegrals

namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge

def unitCochain : Cochain Unit := WithLp.toLp 2 (fun _ => 1)
def unitTrace : Trace 0 0 := .single ()
noncomputable def meanCochain (α : Coefficient) : Cochain Unit := WithLp.toLp 2 (fun _ => mean α)

theorem period_mean_count (α : Coefficient) {a b : Circle} (p : Trace a b) :
    period p (meanCochain α)=mean α*(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change mean α=mean α*((1 : ℤ) : ℝ);rw [Int.cast_one,mul_one]
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add];ring
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg];ring

theorem period_unit_count {a b : Circle} (p : Trace a b) : period p unitCochain=(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change (1 : ℝ)=((1 : ℤ) : ℝ);norm_num
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add]
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg]

theorem count_zero_of_source_ne {a b : Circle} (p : Trace a b) : a≠0 → count p=0 := by
  induction p with
  | refl _ => exact fun _ => rfl
  | single _ => exact fun h => (h rfl).elim
  | trans p q hp hq =>
    intro h
    rw [count,hp h,hq (fun hb => h ((trace_endpoints p).trans hb)),zero_add]
  | symm p hp =>
    intro h
    rw [count,hp (fun ha => h ((trace_endpoints p).symm.trans ha)),neg_zero]

theorem count_homotopic {a b : Circle} (p q : Trace a b)
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

theorem rawIntegral_period (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=mean α*period p unitCochain := by
  rw [rawIntegral_eq_mean_count,period_unit_count]

theorem rawIntegral_harmonic_period (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=period p (meanHarmonic α) := (rawIntegral_eq_mean_count α p).trans (period_mean_count α p).symm

theorem rawIntegral_unit (α : Coefficient) : rawIntegral α unitTrace=mean α := by
  rw [rawIntegral_eq_mean_count]
  simp only [unitTrace,count,Int.cast_one,mul_one]

theorem rawIntegral_refl (α : Coefficient) : rawIntegral α (.refl 0)=0 := by
  simp [rawIntegral_eq_mean_count,count]

theorem rawIntegral_trans (α : Coefficient) (p q : Trace 0 0) :
    rawIntegral α (p.trans q)=rawIntegral α p+rawIntegral α q := by
  simp only [rawIntegral_eq_mean_count,count,Int.cast_add];ring

theorem rawIntegral_symm (α : Coefficient) (p : Trace 0 0) : rawIntegral α p.symm= -rawIntegral α p := by
  simp only [rawIntegral_eq_mean_count,count,Int.cast_neg];ring

theorem rawIntegral_homotopic (α : Coefficient) {p q : Trace 0 0}
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) :
    rawIntegral α p=rawIntegral α q := by
  rw [rawIntegral_eq_mean_count,rawIntegral_eq_mean_count,count_homotopic p q h]

theorem rawIntegral_assoc (α : Coefficient) (p q r : Trace 0 0) :
    rawIntegral α ((p.trans q).trans r)=rawIntegral α (p.trans (q.trans r)) := by
  simp only [rawIntegral_trans];ring

theorem rawIntegral_cancel (α : Coefficient) (p : Trace 0 0) : rawIntegral α (p.trans p.symm)=0 := by
  rw [rawIntegral_trans,rawIntegral_symm,add_neg_cancel]

theorem all_raw_integrals_zero_iff_mean (α : Coefficient) :
    (∀ p : Trace 0 0,rawIntegral α p=0) ↔ mean α=0 := by
  constructor
  · intro h
    exact (rawIntegral_unit α).symm.trans (h unitTrace)
  · intro h p
    simp [rawIntegral_eq_mean_count,h]

theorem unique_harmonic_raw_periods (α : Coefficient) :
    ∃! h : Harmonic (geometricPresentation circleSystem),∀ p : Trace 0 0,rawIntegral α p=period p h := by
  refine ⟨meanHarmonic α,rawIntegral_harmonic_period α,?_⟩
  intro h hh
  apply Subtype.ext
  ext e
  cases e
  have hp := hh unitTrace
  have he : period unitTrace h=h.val () := rfl
  change h.val ()=mean α
  exact ((rawIntegral_unit α).symm.trans (hp.trans he)).symm

end ComputationalHodge.TraceIntegrals
