module

import AUSolution

open Set TopologicalSpace AlexandroffUrysohn
open scoped Topology Uniformity

-- Literal definition values and co-membership are audited separately from theorem types.
example {X : Type*} (C : Set (Set X)) (x y : X) :
    y ∈ pointStar C x ↔ ∃ U ∈ C, x ∈ U ∧ y ∈ U := Iff.rfl

example {X : Type*} (C : Set (Set X)) (x y : X) :
    (x, y) ∈ coverRelation C ↔ ∃ U ∈ C, x ∈ U ∧ y ∈ U := Iff.rfl

-- Empty covers and empty spaces are allowed, without assuming nonempty indices.
example : IsMetrizingSequence (fun _ => (∅ : Set (Set Empty))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨by simp, fun x => nomatch x⟩
  · simp
  · intro x
    exact nomatch x

-- There is no countability restriction on the underlying type or its ball covers.
example {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    ∃ C : ℕ → Set (Set X), IsMetrizingSequence C := exists_metrizingSequence

-- Topology equality and the literal co-membership entourage basis are both conclusions.
example {X : Type*} [t : TopologicalSpace X] [T0Space X]
    {C : ℕ → Set (Set X)} (hC : IsMetrizingSequence C) :
    (∃ u : UniformSpace X, u.toTopologicalSpace = t ∧
      (𝓤[u]).HasBasis (fun _ : ℕ => True) (fun n => coverRelation (C n))) ∧
    (∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t) :=
  ⟨hC.exists_uniformity, exists_compatibleMetric hC⟩

-- A non-T0 space satisfies the cover criterion; the separation-free conclusion
-- must therefore be pseudometrizability rather than metrizability.
section Indiscrete
local instance : TopologicalSpace Bool := ⊤

private theorem indiscrete_sequence :
    IsMetrizingSequence (fun _ => ({univ} : Set (Set Bool))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · intro U hU
      simpa only [mem_singleton_iff.mp hU] using (isOpen_univ : IsOpen (univ : Set Bool))
    · intro x
      exact ⟨univ, mem_singleton _, mem_univ x⟩
  · intro n U hU V hV hUV
    subst U; subst V
    exact ⟨univ, mem_singleton _, by simp⟩
  · intro x O hO hx
    rcases (TopologicalSpace.isOpen_top_iff O).mp hO with h | h
    · simp [h] at hx
    · subst O
      exact ⟨0, subset_univ _⟩

example : PseudoMetrizableSpace Bool := indiscrete_sequence.pseudoMetrizableSpace

example : ¬ MetrizableSpace Bool := by
  intro h
  have : Subsingleton Bool := subsingleton_iff_indiscreteTopology.mpr inferInstance
  exact Bool.false_ne_true (Subsingleton.elim false true)

end Indiscrete
