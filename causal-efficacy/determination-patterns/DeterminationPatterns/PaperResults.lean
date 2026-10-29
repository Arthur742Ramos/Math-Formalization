module
public import DeterminationPatterns.LocalInputs
@[expose] public section
namespace DeterminationPatterns
universe u

/-- For any fixed solution at a legal context, its active determined
vertices are exactly the least solution. -/
theorem active_determined_region_eq_least {α : Type u}
    {C U X : Region α} {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) :
    (fun x => X x ∧ Determined C (Step C D f U) x) = Least (Step C D f U) := by
  funext x
  apply propext
  constructor
  · intro ⟨active, det⟩
    exact active_determinate_is_least adm ctx fixed active det
  · intro hx
    exact ⟨(fixed_bounds fixed).1 hx, Or.inl hx⟩

/-- A unique contextual solution is both the least and greatest solution. -/
theorem unique_contextual_solution_extrema {α : Type u}
    {C U X : Region α} {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (_fixed : Fixed (Step C D f U) X)
    (unique : ∀ Y, Fixed (Step C D f U) Y → Y = X) :
    X = Least (Step C D f U) ∧ X = Greatest (Step C D f U) := by
  constructor
  · exact (unique _ (least_fixed (step_monotone adm U))).symm
  · exact (unique _ (greatest_fixed (step_monotone adm U))).symm

/-- An active determined nonroot has a distinct active root connected by a
finite path entirely in the least solution. -/
theorem active_determined_nonroot_has_distinct_root {α : Type u}
    {C U X : Region α} {D : α → α → Prop} {f : α → Region α → Prop} {a : α}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) (active : X a)
    (det : Determined C (Step C D f U) a) (dependent : ∃ y, Parents C D a y) :
    ∃ b, U b ∧ b ≠ a ∧ InternalPath (Least (Step C D f U)) D b a := by
  obtain ⟨b, hb, path⟩ := active_determinate_internal_root_path adm ctx fixed active det
  refine ⟨b, hb, ?_, path⟩
  intro eq
  subst b
  obtain ⟨y, hy⟩ := dependent
  exact (ctx hb).2 y hy

end DeterminationPatterns
