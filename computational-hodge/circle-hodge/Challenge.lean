module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations

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

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- Algebraic real characters, with the ordinary pointwise vector-space structure. -/
def Characters (S : ContinuousGeometricStepSystem A E) (a : A) :
    Submodule ℝ (representedGroup S a → ℝ) where
  carrier f := f 1 = 0 ∧ ∀ x y, f (x*y) = f x + f y
  zero_mem' := ⟨rfl,fun _ _ => (add_zero _).symm⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨by change f 1 + g 1 = 0; rw [hf.1,hg.1,add_zero],
      fun x y => by change f (x*y)+g (x*y) = (f x+g x)+(f y+g y)
                    rw [hf.2,hg.2]; ring⟩
  smul_mem' := by
    intro r f hf
    exact ⟨by change r*f 1=0; rw [hf.1,mul_zero],
      fun x y => by change r*f (x*y)=r*f x+r*f y; rw [hf.2,mul_add]⟩

/-- These are exactly the usual group homomorphisms to the additive reals. -/
def characterEquivHom (a : A) :
    Characters S a ≃ (representedGroup S a →* Multiplicative ℝ) where
  toFun χ := { toFun := fun g => Multiplicative.ofAdd (χ.val g)
               map_one' := χ.property.1
               map_mul' := χ.property.2 }
  invFun f := ⟨fun g => (f g).toAdd,f.map_one,f.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem character_inv {a : A} (χ : Characters S a) (g : representedGroup S a) :
    χ.val g⁻¹ = -χ.val g := by
  have h := χ.property.2 g g⁻¹
  rw [mul_inv_cancel,χ.property.1] at h
  linarith

end ComputationalHodge.LoopCharacters

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E} {a : A}

def basedTrace (T : Rooting S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y) (hx : Active S a x)
    (hy : Active S a y) : GeometricTrace S.toGeometricStepSystem a a :=
  .trans (.trans (T.trace x hx) p) (.symm (T.trace y hy))

theorem based_refl (T : Rooting S a) {x : A} (hx : Active S a x) :
    representedLoop (basedTrace T (.refl x) hx hx) = 1 := by
  apply Subtype.ext
  change traceClass (basedTrace T (.refl x) hx hx) = _root_.Path.Homotopic.Quotient.refl a
  simp only [basedTrace,traceClass_trans,traceClass_refl,traceClass_symm]
  simp only [_root_.Path.Homotopic.Quotient.trans_refl,
    _root_.Path.Homotopic.Quotient.trans_symm]

theorem based_trans (T : Rooting S a) {x y z : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (q : GeometricTrace S.toGeometricStepSystem y z)
    (hx : Active S a x) (hy : Active S a y) (hz : Active S a z) :
    representedLoop (basedTrace T (.trans p q) hx hz) =
      representedLoop (basedTrace T q hy hz) * representedLoop (basedTrace T p hx hy) := by
  apply Subtype.ext
  change traceClass _ = (traceClass _).trans (traceClass _)
  simp only [basedTrace,traceClass_trans,traceClass_symm,
    _root_.Path.Homotopic.Quotient.trans_assoc]
  rw [← _root_.Path.Homotopic.Quotient.trans_assoc
    (traceClass (T.trace y hy)).symm (traceClass (T.trace y hy))]
  simp only [_root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.refl_trans]

theorem based_symm (T : Rooting S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : Active S a x) (hy : Active S a y) :
    representedLoop (basedTrace T (.symm p) hy hx) =
      (representedLoop (basedTrace T p hx hy))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← based_trans T p (.symm p) hx hy hx]
  apply Subtype.ext
  change traceClass (basedTrace T (.trans p (.symm p)) hx hx) =
    _root_.Path.Homotopic.Quotient.refl a
  simp only [basedTrace,traceClass_trans,traceClass_symm,
    _root_.Path.Homotopic.Quotient.trans_symm,
    _root_.Path.Homotopic.Quotient.trans_refl]

variable [Fintype E]

/-- Recover edge coefficients from the character of actual rooted edge loops. -/
noncomputable def characterCochain (T : Rooting S a) (χ : Characters S a) : Cochain E :=
  WithLp.toLp 2 (fun e => χ.val (representedLoop
    (basedTrace T (.single e) (Or.inr ⟨e,Or.inl rfl⟩) (Or.inr ⟨e,Or.inr rfl⟩))))

theorem characterCochain_period (T : Rooting S a) (χ : Characters S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : Active S a x) (hy : Active S a y) :
    period p (characterCochain T χ) = χ.val (representedLoop (basedTrace T p hx hy)) := by
  induction p with
  | refl x => rw [based_refl,χ.property.1]; rfl
  | single e => rfl
  | @trans x y z p q hp hq =>
    have hm := (active_endpoints p).mp hx
    change period p (characterCochain T χ) + period q (characterCochain T χ) = _
    rw [hp hx hm,hq hm hy,based_trans T p q hx hm hy,χ.property.2,add_comm]
  | symm p hp =>
    change -period p (characterCochain T χ) = _
    rw [hp hy hx,based_symm,character_inv]

theorem characterCochain_closed (T : Rooting S a) (χ : Characters S a) :
    characterCochain T χ ∈ Closed (geometricPresentation S) := by
  classical
  funext c
  change period c.left (characterCochain T χ) - period c.right (characterCochain T χ) = 0
  by_cases hx : Active S a c.src
  · have hy := (active_endpoints c.left).mp hx
    rw [characterCochain_period T χ c.left hx hy,characterCochain_period T χ c.right hx hy]
    apply sub_eq_zero.mpr
    apply congrArg χ.val
    apply Subtype.ext
    change traceClass (basedTrace T c.left hx hy) = traceClass (basedTrace T c.right hx hy)
    simp only [basedTrace,traceClass_trans,traceClass_symm]
    have hc : traceClass c.left = traceClass c.right := _root_.Path.Homotopic.Quotient.eq.mpr c.rule
    rw [hc]
  · rw [inactive_period_zero c.left hx,inactive_period_zero c.right hx,sub_self]

theorem characterCochain_loop (T : Rooting S a) (χ : Characters S a)
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    period p (characterCochain T χ) = χ.val (representedLoop p) := by
  rw [characterCochain_period T χ p (Or.inl rfl) (Or.inl rfl)]
  apply congrArg χ.val
  apply Subtype.ext
  change traceClass (basedTrace T p (Or.inl rfl) (Or.inl rfl)) = traceClass p
  simp only [basedTrace,T.at_root,traceClass_trans,traceClass_refl,traceClass_symm,
    _root_.Path.Homotopic.Quotient.refl_trans]
  change (traceClass p).trans (_root_.Path.Homotopic.Quotient.refl a) = _
  exact _root_.Path.Homotopic.Quotient.trans_refl _

end ComputationalHodge.LoopCharacters

namespace ComputationalHodge.CircleHodge
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters

theorem circle_winding_injective : Function.Injective windingCharacter := by
  let hp := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨0,by simp⟩
  intro g h hh
  apply hp.monodromyPerm_injective
  apply Equiv.ext
  have hm : hp.isCoveringMap.monodromy g e = hp.isCoveringMap.monodromy h e := by
    apply Subtype.ext
    induction g using Quotient.inductionOn with | _ p =>
    induction h using Quotient.inductionOn with | _ q =>
    exact congrArg Multiplicative.toAdd hh
  exact congrFun ((hp.monodromy_ext_iff e).mp hm)

theorem circle_winding_integral (g : FundamentalGroup (AddCircle (1 : ℝ)) 0) :
    ∃ n : ℤ, (n : ℝ) = (windingCharacter g).toAdd := by
  induction g using Quotient.inductionOn with | _ p =>
  have h : ((winding p : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) 1).trans p.target
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h
  refine ⟨n,?_⟩
  change (n : ℝ) = winding p
  simpa using hn

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

def circleRooting : Rooting circleSystem 0 where
  trace x hx := by
    have h : x = 0 := hx.elim id (by rintro ⟨e,h|h⟩ <;> exact h.symm)
    subst x
    exact GeometricTrace.refl 0
  at_root := rfl

noncomputable def circleCharacter : Characters circleSystem 0 :=
  (characterEquivHom 0).symm (windingCharacter.comp (representedGroup circleSystem 0).subtype)

theorem circle_character_generator :
    circleCharacter.val (representedLoop (.single (S := circleSystem.toGeometricStepSystem) ())) = 1 :=
  winding_onceAround

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

/-- A genuine real primitive with its mean term removed. -/
noncomputable def realPotential (α : Coefficient) (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x,cover α t)-x*mean α

theorem realPotential_hasDerivAt (α : Coefficient) (x : ℝ) :
    HasDerivAt (realPotential α) (cover α x-mean α) x := by
  have hi : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u,cover α t) (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  have hm : HasDerivAt (fun u : ℝ => u*mean α) (mean α) x := by
    simpa using (hasDerivAt_id x).mul_const (mean α)
  exact hi.sub hm

theorem realPotential_contDiff (α : Coefficient) : ContDiff ℝ 1 (realPotential α) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (realPotential_hasDerivAt α x).differentiableAt,?_⟩
  have h : deriv (realPotential α)=fun x => cover α x-mean α :=
    funext (fun x => (realPotential_hasDerivAt α x).deriv)
  rw [h]
  exact (cover_continuous α).sub continuous_const

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

theorem potential_cover (α : Coefficient) : cover (potential α)=realPotential α := rfl

theorem potential_zero (α : Coefficient) : potential α 0=0 := by
  change realPotential α 0=0
  simp [realPotential]

theorem potential_contDiff (α : Coefficient) : ContDiff ℝ 1 (cover (potential α)) :=
  realPotential_contDiff α

theorem potential_deriv (α : Coefficient) (x : ℝ) :
    deriv (cover (potential α)) x=cover α x-mean α :=
  (realPotential_hasDerivAt α x).deriv

/-- Exactness requires an actual circle potential and its actual C¹ derivative. -/
def ExactCoefficient (α : Coefficient) : Prop :=
  ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x

/-- Differentiability is essential: `deriv` is totalized at nonsmooth points. -/
def HarmonicCoefficient (α : Coefficient) : Prop :=
  Differentiable ℝ (cover α) ∧ ∀ x,deriv (cover α) x=0

theorem mean_constant (c : ℝ) : mean (constant c)=c := by
  simp [mean,cover,constant]

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

theorem mean_zero_iff_exact (α : Coefficient) : mean α=0 ↔ ExactCoefficient α := by
  constructor
  · intro h
    exact ⟨potential α,potential_contDiff α,fun x => by simpa [h] using potential_deriv α x⟩
  · exact exact_mean_zero

theorem harmonic_iff_constant (α : Coefficient) :
    HarmonicCoefficient α ↔ ∃ c,α=constant c := by
  constructor
  · rintro ⟨hd,hzero⟩
    refine ⟨cover α 0,?_⟩
    apply ContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero hd hzero x 0
  · rintro ⟨c,rfl⟩
    exact ⟨differentiable_const c,fun x => deriv_const x c⟩

theorem residual_exact (α : Coefficient) : ExactCoefficient (α-constant (mean α)) := by
  refine ⟨potential α,potential_contDiff α,fun x => ?_⟩
  exact potential_deriv α x

theorem hodge_decomposition (α : Coefficient) :
    ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ F 0=0 ∧
      ∀ x,cover α x=mean α+deriv (cover F) x := by
  refine ⟨potential α,potential_contDiff α,potential_zero α,fun x => ?_⟩
  rw [potential_deriv]
  ring

theorem unique_harmonic_coefficient (α : Coefficient) :
    ∃! h : Coefficient,HarmonicCoefficient h ∧ ExactCoefficient (α-h) := by
  refine ⟨constant (mean α),⟨(harmonic_iff_constant _).mpr ⟨_,rfl⟩,residual_exact α⟩,?_⟩
  rintro h ⟨hh,he⟩
  obtain ⟨c,rfl⟩ := (harmonic_iff_constant h).mp hh
  have hz := exact_mean_zero he
  rw [mean_sub,mean_constant] at hz
  exact congrArg constant (sub_eq_zero.mp hz).symm

noncomputable def energy (α : Coefficient) : ℝ := ∫ x in (0 : ℝ)..1,(cover α x)^2

theorem mean_orthogonal_residual (α : Coefficient) :
    (∫ x in (0 : ℝ)..1,mean α*(cover α x-mean α))=0 := by
  rw [intervalIntegral.integral_const_mul]
  have h := exact_mean_zero (residual_exact α)
  change (∫ x in (0 : ℝ)..1,cover α x-mean α)=0 at h
  rw [h,mul_zero]

/-- Ordinary analytic energy splits into harmonic mean and exact residual energy. -/
theorem energy_pythagoras (α : Coefficient) :
    energy α=(mean α)^2+energy (α-constant (mean α)) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (mean α)^2) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x => (cover α x-mean α)^2) MeasureTheory.volume 0 1 :=
    (((cover_continuous α).sub continuous_const).pow 2).intervalIntegrable 0 1
  have h3 : IntervalIntegrable (fun x => 2*(mean α*(cover α x-mean α))) MeasureTheory.volume 0 1 :=
    (continuous_const.mul
      (continuous_const.mul ((cover_continuous α).sub continuous_const))).intervalIntegrable 0 1
  calc
    energy α = ∫ x in (0 : ℝ)..1,(mean α)^2+(cover α x-mean α)^2+
        2*(mean α*(cover α x-mean α)) :=
      intervalIntegral.integral_congr (fun x _ => by ring)
    _ = (∫ x in (0 : ℝ)..1,(mean α)^2)+
        (∫ x in (0 : ℝ)..1,(cover α x-mean α)^2)+
        2*(∫ x in (0 : ℝ)..1,mean α*(cover α x-mean α)) := by
      rw [intervalIntegral.integral_add (h1.add h2) h3,
        intervalIntegral.integral_add h1 h2,intervalIntegral.integral_const_mul]
    _ = (mean α)^2+energy (α-constant (mean α)) := by
      rw [mean_orthogonal_residual]
      simp [energy,cover,constant]

end ComputationalHodge.CircleHodge

namespace ComputationalHodge.CircleHodge
open ComputationalHodge.LoopCharacters

/-- An actual C¹ real lift of a based circle loop; corners are not admitted here. -/
structure C1Lift where
  curve : ℝ → ℝ
  smooth : ContDiff ℝ 1 curve
  source : curve 0=0
  target : ((curve 1 : ℝ) : Circle)=0

def projectedLoop (L : C1Lift) : _root_.Path (0 : Circle) 0 where
  toFun t := ((L.curve (t : ℝ) : ℝ) : Circle)
  continuous_toFun := by
    have := L.smooth.continuous
    fun_prop
  source' := by simpa using congrArg (fun x : ℝ => (x : Circle)) L.source
  target' := L.target

theorem projectedLoop_winding (L : C1Lift) : winding (projectedLoop L)=L.curve 1 := by
  have hc : Continuous (fun t : unitInterval => L.curve (t : ℝ)) :=
    L.smooth.continuous.comp continuous_subtype_val
  have h : (⟨fun t : unitInterval => L.curve (t : ℝ),hc⟩ : C(unitInterval,ℝ))=
      circleLift (projectedLoop L) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,L.source⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f 1) h).symm

theorem lift_endpoint_integral (L : C1Lift) : ∃ n : ℤ,(n : ℝ)=L.curve 1 := by
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp L.target
  exact ⟨n,by simpa using hn⟩

/-- Ordinary interval integration of the pulled-back coefficient against velocity. -/
noncomputable def lineIntegral (α : Coefficient) (L : C1Lift) : ℝ :=
  ∫ t in (0 : ℝ)..1,cover α (L.curve t)*deriv L.curve t

theorem lineIntegral_eq_endpoint_integral (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=∫ x in (0 : ℝ)..L.curve 1,cover α x := by
  let A : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u,cover α x
  have ha (x : ℝ) : HasDerivAt A (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  have hd (x : ℝ) : HasDerivAt (fun t => A (L.curve t))
      (cover α (L.curve x)*deriv L.curve x) x :=
    (ha (L.curve x)).comp x ((L.smooth.differentiable (by norm_num)).differentiableAt.hasDerivAt)
  have hc : Continuous (fun t => cover α (L.curve t)*deriv L.curve t) :=
    ((cover_continuous α).comp L.smooth.continuous).mul
      (L.smooth.continuous_deriv (by norm_num))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable 0 1)
  change lineIntegral α L=A (L.curve 1)-A (L.curve 0) at h
  simpa [A,L.source] using h

theorem lineIntegral_eq_mean_endpoint (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=mean α*L.curve 1 := by
  obtain ⟨n,hn⟩ := lift_endpoint_integral L
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq n 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  rw [lineIntegral_eq_endpoint_integral,← hn]
  simpa [mean,zsmul_eq_mul,mul_comm] using h

theorem lineIntegral_eq_winding (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=mean α*(windingCharacter
      (_root_.Path.Homotopic.Quotient.mk (projectedLoop L))).toAdd := by
  change lineIntegral α L=mean α*winding (projectedLoop L)
  rw [projectedLoop_winding]
  exact lineIntegral_eq_mean_endpoint α L

theorem lineIntegral_class_independent (α : Coefficient) (L M : C1Lift)
    (h : _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=
      _root_.Path.Homotopic.Quotient.mk (projectedLoop M)) :
    lineIntegral α L=lineIntegral α M := by
  rw [lineIntegral_eq_winding,lineIntegral_eq_winding,h]

def straightLift (n : ℤ) : C1Lift where
  curve t := (n : ℝ)*t
  smooth := (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (n : ℝ))).mul contDiff_id
  source := by simp
  target := by simp

/-- Every actual ambient class has a smooth representative, proved from winding. -/
theorem smooth_representative (g : FundamentalGroup Circle 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=g := by
  obtain ⟨n,hn⟩ := circle_winding_integral g
  refine ⟨straightLift n,?_⟩
  apply circle_winding_injective
  apply Multiplicative.toAdd.injective
  change winding (projectedLoop (straightLift n))=(windingCharacter g).toAdd
  rw [projectedLoop_winding]
  change (n : ℝ)*1=(windingCharacter g).toAdd
  rw [mul_one]
  exact hn

theorem smooth_period_realization (α : Coefficient) (g : FundamentalGroup Circle 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=g ∧
      lineIntegral α L=mean α*(windingCharacter g).toAdd := by
  obtain ⟨L,hL⟩ := smooth_representative g
  exact ⟨L,hL,by rw [lineIntegral_eq_winding,hL]⟩

theorem exact_lineIntegral_zero {α : Coefficient} (h : ExactCoefficient α) (L : C1Lift) :
    lineIntegral α L=0 := by
  rw [lineIntegral_eq_winding,exact_mean_zero h,zero_mul]

end ComputationalHodge.CircleHodge

namespace ComputationalHodge.CircleHodge
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters

noncomputable def meanCochain (α : Coefficient) : Cochain Unit :=
  characterCochain circleRooting (mean α • circleCharacter)

theorem meanCochain_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    period p (meanCochain α)=mean α*(windingCharacter (traceClass p)).toAdd :=
  characterCochain_loop circleRooting (mean α • circleCharacter) p

theorem meanCochain_unit (α : Coefficient) : meanCochain α ()=mean α := by
  have h := meanCochain_period α (.single ())
  change meanCochain α ()=mean α*winding onceAround at h
  simpa only [winding_onceAround,mul_one] using h

theorem circle_exact_eq_bot : Exact circleSystem=⊥ := by
  apply le_antisymm
  · rintro ω ⟨f,rfl⟩
    change d0 circleSystem.toGeometricStepSystem f=0
    ext e
    exact sub_self (f 0)
  · exact bot_le

/-- A proved member of the existing actual finite harmonic-cochain subspace. -/
noncomputable def harmonicCochain (α : Coefficient) : Harmonic (geometricPresentation circleSystem) :=
  ⟨meanCochain α,characterCochain_closed circleRooting (mean α • circleCharacter),
    by rw [circle_exact_eq_bot,Submodule.bot_orthogonal_eq_top]; trivial⟩

theorem harmonicCochain_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    period p (harmonicCochain α)=mean α*(windingCharacter (traceClass p)).toAdd :=
  meanCochain_period α p

theorem analytic_computational_period (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) (L : C1Lift)
    (h : _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p) :
    lineIntegral α L=period p (harmonicCochain α) := by
  rw [lineIntegral_eq_winding,harmonicCochain_period,h]

/-- Existence is proved; a smooth representative is not supplied as a bridge hypothesis. -/
theorem computational_smooth_realization (α : Coefficient)
    (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p ∧
      lineIntegral α L=period p (harmonicCochain α) := by
  obtain ⟨L,hL⟩ := smooth_representative (traceClass p)
  exact ⟨L,hL,analytic_computational_period α p L hL⟩

theorem zero_harmonic_iff_exact (α : Coefficient) :
    harmonicCochain α=0 ↔ ExactCoefficient α := by
  constructor
  · intro h
    apply (mean_zero_iff_exact α).mp
    have hc := congrArg (fun h : Harmonic (geometricPresentation circleSystem) => h.val ()) h
    simpa [harmonicCochain,meanCochain_unit] using hc
  · intro h
    apply Subtype.ext
    ext e
    cases e
    change meanCochain α ()=0
    rw [meanCochain_unit,exact_mean_zero h]

theorem same_harmonic_iff_exact_difference (α β : Coefficient) :
    harmonicCochain α=harmonicCochain β ↔ ExactCoefficient (α-β) := by
  constructor
  · intro h
    apply (mean_zero_iff_exact _).mp
    rw [mean_sub]
    apply sub_eq_zero.mpr
    have hc := congrArg (fun h : Harmonic (geometricPresentation circleSystem) => h.val ()) h
    simpa [harmonicCochain,meanCochain_unit] using hc
  · intro h
    have hc := exact_mean_zero h
    rw [mean_sub] at hc
    apply Subtype.ext
    ext e
    cases e
    change meanCochain α ()=meanCochain β ()
    rw [meanCochain_unit,meanCochain_unit]
    exact sub_eq_zero.mp hc

theorem harmonicCochain_surjective : Function.Surjective harmonicCochain := by
  intro h
  refine ⟨constant (h.val ()),?_⟩
  apply Subtype.ext
  ext e
  cases e
  change meanCochain (constant (h.val ())) ()=h.val ()
  rw [meanCochain_unit,mean_constant]

theorem all_loop_integrals_zero_iff_exact (α : Coefficient) :
    (∀ L : C1Lift,lineIntegral α L=0) ↔ ExactCoefficient α := by
  constructor
  · intro h
    apply (mean_zero_iff_exact α).mp
    have h1 := h (straightLift 1)
    rw [lineIntegral_eq_mean_endpoint] at h1
    change mean α*(((1 : ℤ) : ℝ)*1)=0 at h1
    simpa only [Int.cast_one,one_mul,mul_one] using h1
  · exact fun h L => exact_lineIntegral_zero h L

theorem unique_computational_harmonic (α : Coefficient) :
    ∃! h : Harmonic (geometricPresentation circleSystem),
      ∀ (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) (L : C1Lift),
        _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p →
          lineIntegral α L=period p h := by
  refine ⟨harmonicCochain α,analytic_computational_period α,?_⟩
  intro h hh
  obtain ⟨L,hL,hI⟩ := computational_smooth_realization α (.single ())
  have hp := (hh (.single ()) L hL).symm.trans hI
  apply Subtype.ext
  ext e
  cases e
  exact hp

end ComputationalHodge.CircleHodge
