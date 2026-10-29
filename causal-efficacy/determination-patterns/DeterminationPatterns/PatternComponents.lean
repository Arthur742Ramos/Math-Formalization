module
public import DeterminationPatterns.Necessity
@[expose] public section
namespace DeterminationPatterns
universe u

/-- An admissible explicit pattern witness has the prescribed extrema. -/
theorem witness_extrema_of_admissible {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D))
    (adm : Mechanism C D (StatusMechanism C D L Z Q)) :
    Least (Step C D (StatusMechanism C D L Z Q) U) = L ∧
      Greatest (Step C D (StatusMechanism C D L Z Q) U) = (fun x => C x ∧ ¬ Z x) := by
  let f := StatusMechanism C D L Z Q
  have fixes := status_two_fixed_points part cond
  have lowFix := least_fixed (step_monotone adm U)
  have highFix := greatest_fixed (step_monotone adm U)
  have lowForces := status_forces_paths part cond ctx lowFix
  have highForces := status_forces_paths part cond ctx highFix
  refine ⟨?_, ?_⟩
  · apply funext
    intro x
    apply propext
    constructor
    · intro hx; exact (fixed_bounds fixes.1).1 hx
    · intro hx; exact lowForces.1 hx
  · apply funext
    intro x
    apply propext
    constructor
    · intro hx; exact highForces.2 hx
    · intro hx; exact (fixed_bounds fixes.2).2 hx

/-- Composition of the necessity, witness-rule and extrema components in the
common Lean model gives the relevant pattern-realization equivalence. -/
theorem exact_pattern_from_components {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Least (Step C D f U) = L ∧
      Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) ↔
      PatternConditions C D U L Z Q := by
  constructor
  · rintro ⟨f, adm, _, low, high⟩
    exact realized_pattern_necessary part ctx adm low high
  · intro cond
    let f := StatusMechanism C D L Z Q
    have adm : Mechanism C D f := status_mechanism_admissible part cond.2.2.2.2
    have rel : Relevant C D f := status_mechanism_relevant part cond.2.2.2.2
    have extrema := witness_extrema_of_admissible part cond ctx adm
    exact ⟨f, adm, rel, extrema.1, extrema.2⟩

end DeterminationPatterns
