module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Analysis.Convex.Contractible

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

namespace ComputationalHodge.TorusPeriods
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

abbrev Torus (E : Type) := E → AddCircle (1 : ℝ)

variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

noncomputable def coordinateLoop (e : E) : _root_.Path (0 : Torus E) 0 where
  toFun t j := if j=e then ((t : ℝ) : AddCircle (1 : ℝ)) else 0
  continuous_toFun := by
    exact continuous_pi (fun j => by
    by_cases h : j=e
    · simp only [h,ite_true]
      fun_prop
    · simpa only [h,ite_false] using (continuous_const : Continuous (fun _ : unitInterval => (0 : AddCircle (1 : ℝ)))))
  source' := by
    funext j
    simp
  target' := by
    funext j
    simp

noncomputable def torusSystem (E : Type) [Fintype E] [TopologicalSpace E] [DiscreteTopology E] [DecidableEq E] :
    ContinuousGeometricStepSystem (Torus E) E where
  src _ := 0
  tgt _ := 0
  realize := coordinateLoop
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def coordinateMap (e : E) :
    FundamentalGroup (Torus E) 0 →* FundamentalGroup (AddCircle (1 : ℝ)) 0 :=
  FundamentalGroup.map ⟨fun x : Torus E => x e,continuous_apply e⟩ (0 : Torus E)

noncomputable def windingVector (g : FundamentalGroup (Torus E) 0) (e : E) : ℝ :=
  (windingCharacter (coordinateMap e g)).toAdd

omit finiteE topE discreteE decidableE in
theorem windingVector_mul (g h : FundamentalGroup (Torus E) 0) (e : E) :
    windingVector (g*h) e = windingVector g e + windingVector h e := by
  unfold windingVector
  rw [map_mul,map_mul]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_inv (g : FundamentalGroup (Torus E) 0) (e : E) :
    windingVector g⁻¹ e = -windingVector g e := by
  unfold windingVector
  rw [map_inv,map_inv]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_one (e : E) : windingVector (1 : FundamentalGroup (Torus E) 0) e = 0 := by
  unfold windingVector
  rw [map_one,map_one]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_injective : Function.Injective (windingVector (E := E)) := by
  intro g h heq
  have hc : (fun e => _root_.Path.Homotopic.proj e g) = fun e => _root_.Path.Homotopic.proj e h := by
    funext e
    apply circle_winding_injective
    exact Multiplicative.toAdd.injective (congrFun heq e)
  exact (_root_.Path.Homotopic.pi_proj g).symm.trans
    ((congrArg _root_.Path.Homotopic.pi hc).trans (_root_.Path.Homotopic.pi_proj h))

theorem coordinate_winding (i j : E) :
    windingVector (traceClass (S := torusSystem E) (.single i)) j = if i=j then 1 else 0 := by
  classical
  have h : (coordinateLoop i).map (continuous_apply j) =
      (if i=j then onceAround else _root_.Path.refl 0) := by
    by_cases hij : i=j
    · subst j
      ext t
      simp [coordinateLoop,onceAround]
      rfl
    · ext t; simp [coordinateLoop,hij,Ne.symm hij]
  change (windingCharacter (_root_.Path.Homotopic.Quotient.mk
    ((coordinateLoop i).map (continuous_apply j)))).toAdd = _
  rw [h]
  split_ifs
  · exact winding_onceAround
  · exact winding_refl

end ComputationalHodge.TorusPeriods

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

namespace ComputationalHodge.TorusPeriods
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

/-- Ordinary algebraic real characters of the entire ambient fundamental group. -/
def AmbientCharacters (E : Type) : Submodule ℝ (FundamentalGroup (Torus E) 0 → ℝ) where
  carrier f := f 1=0 ∧ ∀ g h,f (g*h)=f g+f h
  zero_mem' := ⟨rfl,fun _ _ => (add_zero _).symm⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨by change f 1+g 1=0; rw [hf.1,hg.1,add_zero],
      fun x y => by change f (x*y)+g (x*y)=(f x+g x)+(f y+g y); rw [hf.2,hg.2]; ring⟩
  smul_mem' := by
    intro r f hf
    exact ⟨by change r*f 1=0; rw [hf.1,mul_zero],
      fun x y => by change r*f (x*y)=r*f x+r*f y; rw [hf.2,mul_add]⟩

def ambientCharacterEquivHom :
    AmbientCharacters E ≃ (FundamentalGroup (Torus E) 0 →* Multiplicative ℝ) where
  toFun χ := {toFun := fun g => Multiplicative.ofAdd (χ.val g)
              map_one' := χ.property.1
              map_mul' := χ.property.2}
  invFun f := ⟨fun g => (f g).toAdd,f.map_one,f.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def ambientPeriod (ω : Cochain E) : AmbientCharacters E :=
  ⟨fun g => ∑ e,ω e * windingVector g e,
   by
     change (∑ e,ω e*windingVector (1 : FundamentalGroup (Torus E) 0) e)=0
     simp only [windingVector_one,mul_zero,Finset.sum_const_zero],
   by
     intro g h
     change (∑ e,ω e*windingVector (g*h) e) =
       (∑ e,ω e*windingVector g e)+(∑ e,ω e*windingVector h e)
     simp only [windingVector_mul,mul_add,Finset.sum_add_distrib]⟩

theorem ambientPeriod_coordinate (ω : Cochain E) (e : E) :
    (ambientPeriod ω).val (traceClass (S := torusSystem E) (.single e)) = ω e := by
  simp [ambientPeriod,coordinate_winding]

noncomputable def torusRooting : Rooting (torusSystem E) 0 where
  trace x hx := by
    have h : x=0 := hx.elim id (by rintro ⟨e,h|h⟩ <;> exact h.symm)
    subst x
    exact .refl 0
  at_root := rfl

noncomputable def restrictCharacter (χ : AmbientCharacters E) : Characters (torusSystem E) 0 :=
  ⟨fun g => χ.val g.val,χ.property.1,fun g h => χ.property.2 g.val h.val⟩

noncomputable def reconstructed (χ : AmbientCharacters E) : Cochain E :=
  characterCochain torusRooting (restrictCharacter χ)

theorem reconstructed_coordinate (χ : AmbientCharacters E) (e : E) :
    reconstructed χ e = χ.val (traceClass (S := torusSystem E) (.single e)) :=
  characterCochain_loop torusRooting (restrictCharacter χ) (.single e)

theorem reconstructed_period (χ : AmbientCharacters E)
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    period p (reconstructed χ) = χ.val (traceClass p) :=
  characterCochain_loop torusRooting (restrictCharacter χ) p

theorem reconstructed_ambientPeriod (ω : Cochain E) : reconstructed (ambientPeriod ω) = ω := by
  ext e
  exact (reconstructed_coordinate _ e).trans (ambientPeriod_coordinate ω e)

theorem torus_closed_eq_top : Closed (geometricPresentation (torusSystem E)) = ⊤ := by
  apply top_unique
  intro ω _
  rw [← reconstructed_ambientPeriod ω]
  exact characterCochain_closed torusRooting (restrictCharacter (ambientPeriod ω))

theorem torus_exact_eq_bot : Exact (torusSystem E) = ⊥ := by
  apply le_antisymm
  · rintro ω ⟨f,rfl⟩
    change d0 (torusSystem E).toGeometricStepSystem f = 0
    ext e
    exact sub_self (f 0)
  · exact bot_le

theorem torus_harmonic_eq_top : Harmonic (geometricPresentation (torusSystem E)) = ⊤ := by
  rw [Harmonic,torus_closed_eq_top,torus_exact_eq_bot]
  simp

noncomputable def harmonicCoefficients (ω : Cochain E) : Harmonic (geometricPresentation (torusSystem E)) :=
  ⟨ω,by rw [torus_harmonic_eq_top]; trivial⟩

end ComputationalHodge.TorusPeriods

namespace ComputationalHodge.TorusPeriods
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

omit finiteE topE discreteE decidableE in
theorem windingVector_zpow (g : FundamentalGroup (Torus E) 0) (n : ℤ) (e : E) :
    windingVector (g^n) e = (n : ℝ)*windingVector g e := by
  unfold windingVector
  rw [map_zpow,map_zpow]
  simp

/-- Finite products of integer powers of actual coordinate loops realize every
integer winding vector supported on a finite set. Membership retains a genuine trace witness. -/
theorem finite_winding_realization (s : Finset E) (z : E → ℤ) :
    ∃ g : representedGroup (torusSystem E) 0,
      ∀ j, windingVector g.val j = if j ∈ s then (z j : ℝ) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1,fun j => ?_⟩
    change windingVector (1 : FundamentalGroup (Torus E) 0) j = _
    rw [windingVector_one]
    simp
  | @insert e s he ih =>
    obtain ⟨g,hg⟩ := ih
    let k : representedGroup (torusSystem E) 0 := representedLoop (.single e)
    refine ⟨k^(z e)*g,fun j => ?_⟩
    change windingVector (k.val^(z e)*g.val) j = _
    rw [windingVector_mul,windingVector_zpow]
    change (z e : ℝ)*windingVector (traceClass (S := torusSystem E) (.single e)) j+
      windingVector g.val j = _
    rw [coordinate_winding,hg]
    by_cases hje : j=e
    · subst j
      simp [he]
    · simp [hje,Ne.symm hje]

/-- All ambient torus loop classes have actual finite computational representatives. -/
theorem every_ambient_class_represented (g : FundamentalGroup (Torus E) 0) :
    ∃ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0, traceClass p=g := by
  classical
  have hi : ∀ e, ∃ n : ℤ, (n : ℝ)=windingVector g e :=
    fun e => circle_winding_integral (coordinateMap e g)
  choose z hz using hi
  obtain ⟨k,hk⟩ := finite_winding_realization Finset.univ z
  have h : k.val=g := windingVector_injective (by
    funext e
    simpa [hz] using hk e)
  exact k.property.imp (fun _ hp => hp.trans h)

theorem torus_represented_eq_top : representedGroup (torusSystem E) 0 = ⊤ := by
  apply top_unique
  intro g _
  exact every_ambient_class_represented g

/-- Reconstruction is exact on all ambient characters because coordinate traces
generate the entire ambient group, rather than just a stipulated presented group. -/
theorem ambientPeriod_reconstructed (χ : AmbientCharacters E) :
    ambientPeriod (reconstructed χ)=χ := by
  apply Subtype.ext
  funext g
  obtain ⟨p,rfl⟩ := every_ambient_class_represented g
  have h := reconstructed_period (ambientPeriod (reconstructed χ)) p
  rw [reconstructed_ambientPeriod] at h
  exact h.symm.trans (reconstructed_period χ p)

theorem ambientPeriod_loop (ω : Cochain E)
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    (ambientPeriod ω).val (traceClass p)=period p ω := by
  have h := reconstructed_period (ambientPeriod ω) p
  rw [reconstructed_ambientPeriod] at h
  exact h.symm

noncomputable def ambientPeriodLinear : Cochain E →ₗ[ℝ] AmbientCharacters E where
  toFun := ambientPeriod
  map_add' ω η := by
    apply Subtype.ext
    funext g
    change (∑ e,(ω+η) e*windingVector g e) = _
    simp [ambientPeriod,add_mul,Finset.sum_add_distrib]
  map_smul' r ω := by
    apply Subtype.ext
    funext g
    change (∑ e,(r • ω) e*windingVector g e) = _
    simp [ambientPeriod,Finset.mul_sum,mul_assoc]

/-- The actual finite cochain space is linearly equivalent to all ordinary
algebraic real characters of the ambient torus fundamental group. -/
noncomputable def cochainAmbientEquiv : Cochain E ≃ₗ[ℝ] AmbientCharacters E :=
  LinearEquiv.ofBijective ambientPeriodLinear
    ⟨fun ω η h => (reconstructed_ambientPeriod ω).symm.trans
      ((congrArg reconstructed h).trans (reconstructed_ambientPeriod η)),
     fun χ => ⟨reconstructed χ,ambientPeriod_reconstructed χ⟩⟩

noncomputable def harmonicAmbientEquiv :
    Harmonic (geometricPresentation (torusSystem E)) ≃ₗ[ℝ] AmbientCharacters E :=
  LinearEquiv.ofBijective (ambientPeriodLinear.comp (Submodule.subtype _))
    ⟨fun _ _ hh => Subtype.ext (cochainAmbientEquiv.injective hh),
     fun χ => ⟨harmonicCoefficients (reconstructed χ),ambientPeriod_reconstructed χ⟩⟩

theorem harmonicAmbientEquiv_loop
    (h : Harmonic (geometricPresentation (torusSystem E)))
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    (harmonicAmbientEquiv h).val (traceClass p)=period p h :=
  ambientPeriod_loop (h : Cochain E) p

theorem ambient_character_formula (χ : AmbientCharacters E)
    (g : FundamentalGroup (Torus E) 0) :
    χ.val g = ∑ e,χ.val (traceClass (S := torusSystem E) (.single e))*windingVector g e := by
  have h := congrArg (fun ψ : AmbientCharacters E => ψ.val g) (ambientPeriod_reconstructed χ)
  change (∑ e,reconstructed χ e*windingVector g e)=χ.val g at h
  simpa only [reconstructed_coordinate] using h.symm

theorem cochainAmbientEquiv_inverse_coordinate (χ : AmbientCharacters E) (e : E) :
    (cochainAmbientEquiv.symm χ) e = χ.val (traceClass (S := torusSystem E) (.single e)) := by
  have h := reconstructed_ambientPeriod (cochainAmbientEquiv.symm χ)
  change reconstructed (cochainAmbientEquiv (cochainAmbientEquiv.symm χ)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrArg (fun ω : Cochain E => ω e) h).symm.trans (reconstructed_coordinate χ e)

theorem unique_harmonic_ambient_character (χ : AmbientCharacters E) :
    ∃! h : Harmonic (geometricPresentation (torusSystem E)),
      ∀ g, (harmonicAmbientEquiv h).val g=χ.val g := by
  refine ⟨harmonicAmbientEquiv.symm χ,fun g => ?_,fun h hh => ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
  · apply harmonicAmbientEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (funext hh)

theorem unique_harmonic_loop_periods (χ : AmbientCharacters E) :
    ∃! h : Harmonic (geometricPresentation (torusSystem E)),
      ∀ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0,
        period p h=χ.val (traceClass p) := by
  refine ⟨harmonicAmbientEquiv.symm χ,fun p => ?_,fun h hh => ?_⟩
  · rw [← harmonicAmbientEquiv_loop,LinearEquiv.apply_symm_apply]
  · apply harmonicAmbientEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext g
    obtain ⟨p,rfl⟩ := every_ambient_class_represented g
    exact (harmonicAmbientEquiv_loop h p).trans (hh p)

/-- The zero-dimensional torus needs no nonempty-index assumption. -/
theorem empty_index_character_zero [IsEmpty E] (χ : AmbientCharacters E)
    (g : FundamentalGroup (Torus E) 0) : χ.val g=0 := by
  rw [ambient_character_formula]
  simp

end ComputationalHodge.TorusPeriods
