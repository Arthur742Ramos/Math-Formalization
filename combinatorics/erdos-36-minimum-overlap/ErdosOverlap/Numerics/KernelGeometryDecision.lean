/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierPolynomialDirectFast

public section
namespace ErdosOverlap.FrontierLeaves
open ErdosOverlap.Numerics

/-- Prove the original geometry conditions by kernel reduction. -/
macro "erdos_geometry_decide" : tactic =>
  `(tactic| (
    rw [← Geometry.directTraceCheckFast_eq]
    simp only [Geometry.directTraceCheckFast, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · decide +kernel
    · simp only [CachedPolynomialTrace.directCheckFast,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
    · simp only [CachedPolynomialTrace.directCheckFast,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
    · decide +kernel
  ))

end ErdosOverlap.FrontierLeaves
