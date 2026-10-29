module
public import DeterminationPatterns.Quantifiers
@[expose] public section
namespace DeterminationPatterns
universe u

/-- At every legal context and for every admissible mechanism, all accessible
vertices are determined and all determined vertices are root-reachable. -/
theorem contextual_determination_interval {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    Sub (AccessibleRegion C D) (Determined C (Step C D f U)) ∧
      Sub (Determined C (Step C D f U)) (RootReachable C D) := by
  have reg := determined_region_conditions adm ctx
  exact ⟨accessible_subset_region reg, region_subset_reachable reg⟩

/-- At a fixed legal context, both endpoints of the determination interval
are attained by fully edge-relevant admissible mechanisms. The witnesses may differ. -/
theorem relevant_endpoint_attainment {α : Type u} {C U : Region α}
    {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    ∃ f g, Mechanism C D f ∧ Relevant C D f ∧
      Determined C (Step C D f U) = AccessibleRegion C D ∧
      Mechanism C D g ∧ Relevant C D g ∧
      Determined C (Step C D g U) = RootReachable C D := by
  obtain ⟨f, admF, relF, eqF⟩ := region_conditions_sufficient (accessible_region_conditions C D) ctx
  obtain ⟨g, admG, relG, eqG⟩ := region_conditions_sufficient (root_reachable_conditions C D) ctx
  exact ⟨f, g, admF, relF, eqF, admG, relG, eqG⟩

end DeterminationPatterns
