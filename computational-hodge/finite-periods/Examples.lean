module

public import PeriodSeparation
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section
namespace ComputationalHodge.ParallelEdges
open ComputationalPaths.Path.GeometricTopology

scoped instance edgeTopology : TopologicalSpace (Fin 2) := ⊥

/-- Two distinct computational generators with the same real-line realization. -/
noncomputable def system : ContinuousGeometricStepSystem ℝ (Fin 2) where
  src _ := 0
  tgt _ := 1
  realize _ := _root_.Path.segment 0 1
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_const

def freePresentation : ScopedGeometricRewritePresentation system where
  rule _ _ := False
  sound_rule h := False.elim h

abbrev leftEdge : GeometricTrace system.toGeometricStepSystem (0 : ℝ) 1 := .single 0
abbrev rightEdge : GeometricTrace system.toGeometricStepSystem (0 : ℝ) 1 := .single 1
abbrev loop : GeometricTrace system.toGeometricStepSystem (0 : ℝ) 0 :=
  .trans leftEdge (.symm rightEdge)

def omega : Cochain (Fin 2) := WithLp.toLp 2 ![1, -1]

theorem all_closed (ω : Cochain (Fin 2)) : ω ∈ Closed freePresentation := by
  funext c
  exact False.elim c.rule

theorem harmonic_iff (ω : Cochain (Fin 2)) :
    ω ∈ Harmonic freePresentation ↔ ω 0 + ω 1 = 0 := by
  constructor
  · intro h
    have he : d0 system.toGeometricStepSystem (fun x : ℝ => x) ∈ Exact system := ⟨_, rfl⟩
    have hi := (Submodule.mem_orthogonal _ _).mp h.2 _ he
    simpa [PiLp.inner_apply, Fin.sum_univ_two, d0, system] using hi
  · intro h
    refine ⟨all_closed ω, ?_⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨f, rfl⟩
    simp [PiLp.inner_apply, Fin.sum_univ_two, d0, system]
    rw [← add_mul, h, zero_mul]

theorem omega_harmonic : omega ∈ Harmonic freePresentation := by
  apply (harmonic_iff omega).mpr
  norm_num [omega]

theorem omega_loop_period : period loop omega = 2 := by
  change (1 : ℝ) - (-1) = 2
  norm_num

theorem omega_not_exact : omega ∉ Exact system := by
  intro h
  have hz := (exact_iff_zero_loop_periods omega).mp h 0 loop
  rw [omega_loop_period] at hz
  norm_num at hz

/-- This computational loop is nevertheless geometrically null-homotopic. -/
theorem loop_geometrically_null :
    _root_.Path.Homotopic (GeometricTrace.realize loop) (_root_.Path.refl 0) :=
  ⟨(_root_.Path.Homotopy.reflTransSymm (_root_.Path.segment (0 : ℝ) 1)).symm⟩

inductive ParallelRule : {a b : ℝ} →
    GeometricTrace system.toGeometricStepSystem a b →
    GeometricTrace system.toGeometricStepSystem a b → Prop
  | identify : ParallelRule leftEdge rightEdge

/-- Add the one genuine, geometrically sound, parallel-generator rewrite. -/
def parallelPresentation : ScopedGeometricRewritePresentation system where
  rule := ParallelRule
  sound_rule h := by
    cases h
    exact ⟨_root_.Path.Homotopy.refl (_root_.Path.segment (0 : ℝ) 1)⟩

theorem parallel_closed_equal (ω : Closed parallelPresentation) : ω.val 0 = ω.val 1 :=
  closed_rule parallelPresentation ω ParallelRule.identify

theorem parallel_harmonic_zero (ω : Harmonic parallelPresentation) : ω = 0 := by
  have heq := parallel_closed_equal ⟨ω, ω.property.1⟩
  change ω.val 0 = ω.val 1 at heq
  have hsum : (ω : Cochain (Fin 2)) 0 + ω.val 1 = 0 := by
    apply (harmonic_iff (ω : Cochain (Fin 2))).mp
    exact ⟨all_closed ω, ω.property.2⟩
  have h0 : ω.val 0 = 0 := by linarith
  have h1 : ω.val 1 = 0 := by linarith
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem rewrite_changes_periods :
    ScopedRwEq parallelPresentation leftEdge rightEdge ∧
      ¬ScopedRwEq freePresentation leftEdge rightEdge := by
  refine ⟨.generator ParallelRule.identify, ?_⟩
  intro h
  have hi := period_rewrite freePresentation ⟨omega, all_closed omega⟩ h
  change (1 : ℝ) = -1 at hi
  linarith

end ComputationalHodge.ParallelEdges
