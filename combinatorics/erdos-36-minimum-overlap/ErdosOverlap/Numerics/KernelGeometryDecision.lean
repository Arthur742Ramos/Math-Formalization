/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierPolynomialDirectTrace

public section
namespace ErdosOverlap.FrontierLeaves
open ErdosOverlap.Numerics

/-- Prove every original geometry condition with ordinary kernel decisions,
then combine them. Splitting avoids repeatedly reducing a large conjunction. -/
macro "erdos_geometry_decide" : tactic =>
  `(tactic| (
    simp only [Geometry.directTraceCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · decide +kernel
    · simp only [CachedPolynomialTrace.directCheck, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
    · simp only [CachedPolynomialTrace.directCheck, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
    · decide +kernel
  ))

end ErdosOverlap.FrontierLeaves
