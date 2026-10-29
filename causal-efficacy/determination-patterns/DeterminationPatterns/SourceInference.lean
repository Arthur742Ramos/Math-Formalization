module
public import DeterminationPatterns.LabelledSpine
@[expose] public section
namespace DeterminationPatterns
universe u

def EfficacyStep {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (X : Region α) : Region α :=
  fun x => C x ∧ f x (fun y => X y ∧ Parents C D x y)

theorem all_roots_context_is_original {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (adm : Mechanism C D f) :
    Step C D f (Roots C D) = EfficacyStep C D f := by
  classical
  funext X x
  apply propext
  constructor
  · intro h
    rcases h with hr | ⟨hc, _, hf⟩
    · refine ⟨hr.1, ?_⟩
      have eq : (fun y => X y ∧ Parents C D x y) = (fun _ => False) := by
        funext y; apply propext
        exact ⟨fun h => hr.2 y h.2, fun h => False.elim h⟩
      rw [eq]
      exact (adm x hr.1).2.1.mpr hr.2
    · exact ⟨hc, hf⟩
  · rintro ⟨hc, hf⟩
    by_cases hp : ∃ y, Parents C D x y
    · exact Or.inr ⟨hc, hp, hf⟩
    · exact Or.inl ⟨hc, fun y hy => hp ⟨y, hy⟩⟩

theorem source_generated_target_has_root_ancestor {α : Type u}
    {C : Region α} {D : α → α → Prop} {f : α → Region α → Prop} {a : α}
    (adm : Mechanism C D f) (active : Least (EfficacyStep C D f) a) :
    ∃ b, FirstMember C D b a := by
  let U := Roots C D
  have ctx : Sub U (Roots C D) := by intro _ h; exact h
  have lpath := contextual_least_internal_paths adm ctx
  rw [all_roots_context_is_original adm] at lpath
  have hl : InternalReach (Least (EfficacyStep C D f)) D U a := by rw [lpath]; exact active
  have lf : Fixed (Step C D f U) (Least (Step C D f U)) := least_fixed (step_monotone adm U)
  have lc : Sub (Least (EfficacyStep C D f)) C := by
    rw [← all_roots_context_is_original adm]
    exact contextual_fixed_carrier ctx lf
  have reach : RootReachable C D a := reach_weaken lc (fun _ h => h) hl
  exact (root_reachable_iff_first_member C D a).mp reach

theorem nonempty_source_generated_targets_have_root {α : Type u}
    {C T : Region α} {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (nonempty : ∃ a, T a)
    (active : Sub T (Least (EfficacyStep C D f))) : ∃ b, Roots C D b := by
  obtain ⟨a, ha⟩ := nonempty
  obtain ⟨b, _, root⟩ := source_generated_target_has_root_ancestor adm (active ha)
  exact ⟨b, root⟩

def FirstCause {α : Type u} (C : Region α) (D : α → α → Prop) (b a : α) : Prop :=
  FirstMember C D b a ∧ b ≠ a

theorem dependent_source_generated_target_has_distinct_root {α : Type u}
    {C : Region α} {D : α → α → Prop} {f : α → Region α → Prop} {a : α}
    (adm : Mechanism C D f) (active : Least (EfficacyStep C D f) a)
    (dependent : Grounded C D a) : ∃ b, FirstCause C D b a := by
  obtain ⟨b, first⟩ := source_generated_target_has_root_ancestor adm active
  refine ⟨b, first, ?_⟩
  intro eq
  subst b
  obtain ⟨y, hyC, hyD⟩ := dependent.2
  exact first.2.2 y ⟨hyC, hyD⟩

end DeterminationPatterns
