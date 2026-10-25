module
public import Chains
@[expose] public section
namespace ComputationalHodge.PresentationHomology
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def ChainBoundaries (P : ScopedGeometricRewritePresentation S) :
    Submodule ℝ (Cycles S.toGeometricStepSystem) :=
  (Relations P).comap (Cycles S.toGeometricStepSystem).subtype
abbrev ChainH1 (P : ScopedGeometricRewritePresentation S) :=
  Cycles S.toGeometricStepSystem ⧸ ChainBoundaries P


end ComputationalHodge.PresentationHomology
