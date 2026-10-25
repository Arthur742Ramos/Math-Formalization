module
public import PeriodSeparation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
@[expose] public section
namespace ComputationalHodge.PresentationHomology
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E]

noncomputable def wordChain {S : GeometricStepSystem A E} {a b : A} :
    GeometricTrace S a b → Cochain E
  | .refl _ => 0
  | .single e => EuclideanSpace.basisFun E ℝ e
  | .trans p q => wordChain p + wordChain q
  | .symm p => -wordChain p

theorem wordChain_period {S : GeometricStepSystem A E} {a b : A}
    (p : GeometricTrace S a b) (ω : Cochain E) : inner ℝ (wordChain p) ω = period p ω := by
  induction p with
  | refl a => simp [wordChain, period]
  | single e => exact EuclideanSpace.basisFun_inner E ℝ ω e
  | trans p q hp hq => simp [wordChain, period, inner_add_left, hp, hq]
  | symm p hp => simp [wordChain, period, hp]

noncomputable def boundary₁ (S : GeometricStepSystem A E) : Cochain E →ₗ[ℝ] (A →₀ ℝ) :=
  (EuclideanSpace.basisFun E ℝ).toBasis.constr ℝ
    (fun e => Finsupp.single (S.tgt e) 1 - Finsupp.single (S.src e) 1)

theorem boundary_word {S : GeometricStepSystem A E} {a b : A} (p : GeometricTrace S a b) :
    boundary₁ S (wordChain p) = Finsupp.single b 1 - Finsupp.single a 1 := by
  induction p with
  | refl a => simp [wordChain]
  | single e => exact (EuclideanSpace.basisFun E ℝ).toBasis.constr_basis ℝ _ e
  | trans p q hp hq => simp only [wordChain, map_add, hp, hq]; abel
  | symm p hp => simp only [wordChain, map_neg, hp]; abel

noncomputable def vertexEval (f : A → ℝ) : (A →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ f

theorem boundary_pair (S : GeometricStepSystem A E) (f : A → ℝ) (z : Cochain E) :
    vertexEval f (boundary₁ S z) = inner ℝ (d0 S f) z := by
  have h : (vertexEval f).comp (boundary₁ S) = (innerSL ℝ (d0 S f)).toLinearMap := by
    apply (EuclideanSpace.basisFun E ℝ).toBasis.ext
    intro e
    change vertexEval f (boundary₁ S ((EuclideanSpace.basisFun E ℝ) e)) =
      inner ℝ (d0 S f) ((EuclideanSpace.basisFun E ℝ) e)
    rw [EuclideanSpace.inner_basisFun_real,
      show boundary₁ S ((EuclideanSpace.basisFun E ℝ) e) = _ from
        (EuclideanSpace.basisFun E ℝ).toBasis.constr_basis ℝ _ e]
    simp [vertexEval, d0]
  exact LinearMap.congr_fun h z

noncomputable def Cycles (S : GeometricStepSystem A E) : Submodule ℝ (Cochain E) :=
  LinearMap.ker (boundary₁ S)

variable [TopologicalSpace E] {S : ContinuousGeometricStepSystem A E}

theorem cycles_eq_exact_orthogonal : Cycles S.toGeometricStepSystem = (Exact S)ᗮ := by
  classical
  ext z
  constructor
  · intro hz u hu
    rcases hu with ⟨f, rfl⟩
    rw [← boundary_pair, show boundary₁ S.toGeometricStepSystem z = 0 from hz, map_zero]
  · intro hz
    apply Finsupp.ext
    intro a
    have h := hz (d0 S.toGeometricStepSystem (Pi.single a 1)) ⟨_, rfl⟩
    rw [← boundary_pair] at h
    simpa [vertexEval] using h

noncomputable def boundary₂ (P : ScopedGeometricRewritePresentation S) :
    (Cell P →₀ ℝ) →ₗ[ℝ] Cochain E :=
  Finsupp.linearCombination ℝ (fun c => wordChain c.left - wordChain c.right)

noncomputable def Relations (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Cochain E) :=
  LinearMap.range (boundary₂ P)

theorem relations_eq_span (P : ScopedGeometricRewritePresentation S) :
    Relations P = Submodule.span ℝ (Set.range fun c : Cell P => wordChain c.left - wordChain c.right) :=
  Finsupp.range_linearCombination ℝ

theorem boundary_squared (P : ScopedGeometricRewritePresentation S) :
    (boundary₁ S.toGeometricStepSystem).comp (boundary₂ P) = 0 := by
  apply Finsupp.lhom_ext
  intro c r
  simp [boundary₂, boundary_word]

theorem relations_le_cycles (P : ScopedGeometricRewritePresentation S) :
    Relations P ≤ Cycles S.toGeometricStepSystem := by
  rintro z ⟨c, rfl⟩
  exact LinearMap.congr_fun (boundary_squared P) c

theorem closed_eq_relations_orthogonal (P : ScopedGeometricRewritePresentation S) :
    Closed P = (Relations P)ᗮ := by
  ext ω
  constructor
  · intro hω z hz
    have h : Relations P ≤ LinearMap.ker (innerSL ℝ ω).toLinearMap := by
      rw [relations_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨c, rfl⟩
      change inner ℝ ω (wordChain c.left - wordChain c.right) = 0
      rw [real_inner_comm, inner_sub_left, wordChain_period, wordChain_period]
      exact congrFun hω c
    exact (real_inner_comm _ _).trans (h hz)
  · intro hω
    funext c
    change period c.left ω - period c.right ω = 0
    have hc : wordChain c.left - wordChain c.right ∈ Relations P := by
      rw [relations_eq_span]
      exact Submodule.subset_span ⟨c, rfl⟩
    exact (by simpa [inner_sub_left, wordChain_period] using hω _ hc)

noncomputable def LoopSpan (S : GeometricStepSystem A E) : Submodule ℝ (Cochain E) :=
  Submodule.span ℝ (Set.range fun l : Σ a, GeometricTrace S a a => wordChain l.2)

theorem loopSpan_orthogonal : (LoopSpan S.toGeometricStepSystem)ᗮ = Exact S := by
  ext ω
  rw [exact_iff_zero_loop_periods]
  constructor
  · intro h a p
    exact (wordChain_period p ω).symm.trans (h _ (Submodule.subset_span ⟨⟨a,p⟩,rfl⟩))
  · intro h
    have hs : LoopSpan S.toGeometricStepSystem ≤ LinearMap.ker (innerSL ℝ ω).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,p⟩,rfl⟩
      change inner ℝ ω (wordChain p) = 0
      rw [real_inner_comm, wordChain_period, h a p]
    intro z hz
    exact (real_inner_comm _ _).trans (hs hz)

theorem loopSpan_eq_cycles : LoopSpan S.toGeometricStepSystem = Cycles S.toGeometricStepSystem := by
  rw [cycles_eq_exact_orthogonal, ← loopSpan_orthogonal, Submodule.orthogonal_orthogonal]

end ComputationalHodge.PresentationHomology
