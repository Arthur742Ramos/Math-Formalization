module

public import SourcePaths
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
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

/-- Closedness propagates through the full upstream scoped rewrite derivation. -/
theorem period_rewrite (P : ScopedGeometricRewritePresentation S) (ω : Closed P)
    {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : ScopedRwEq P p q) : period p ω = period q ω := by
  induction h with
  | refl _ => rfl
  | generator h => exact closed_rule P ω h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | trans_congr _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | symm_congr _ ih => exact congrArg Neg.neg ih
  | refl_trans p => exact zero_add _
  | trans_refl p => exact add_zero _
  | trans_assoc p q r => exact add_assoc _ _ _
  | symm_trans p => exact neg_add_cancel _
  | trans_symm p => exact add_neg_cancel _
  | symm_symm p => exact neg_neg _
  | symm_refl a => exact neg_zero
  | symm_comp p q =>
    change -(period p ω + period q ω) = -period q ω + -period p ω
    ring

def pathSetoid (P : ScopedGeometricRewritePresentation S) (a b : A) :
    Setoid (GeometricTrace S.toGeometricStepSystem a b) where
  r := ScopedRwEq P
  iseqv := ⟨ScopedRwEq.refl, ScopedRwEq.symm, ScopedRwEq.trans⟩

abbrev PathClass (P : ScopedGeometricRewritePresentation S) (a b : A) :=
  Quotient (pathSetoid P a b)

end ComputationalHodge
