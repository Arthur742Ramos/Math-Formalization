module
public import DeterminationPatterns.PaperExamples
@[expose] public section

/-! The manuscript's concrete removed-portion groundedness illustrations. -/
namespace DeterminationPatterns

theorem rootless_all_on_whole_portion_unfed :
    ¬ ∃ x, (fun _ : Nat => True) x ∧
      Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism (fun _ => False)
        (fun _ : Nat => True ∧ ¬ True) x := by
  rintro ⟨x, _, hx⟩
  exact ((rootless_copy_step _ x).mp hx).2 True.intro

theorem rootless_all_on_not_supported :
    ¬ Supported (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
      (fun _ => False)) (fun _ => True) := by
  intro supported
  apply rootless_all_on_whole_portion_unfed
  exact supported (fun _ => True) (fun _ h => h) ⟨0, True.intro⟩

def FigureLinks : Region (LabelNode Unit) := fun x =>
  match x with
  | .root _ => False
  | .link _ => True

theorem figure_and_on_all_links_unfed :
    ¬ ∃ x, FigureLinks x ∧
      Step (fun _ => True) (LabelDependency FigureLabel)
        (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext true))
        (fun y => LabelState (FigureContext true) (fun _ => True) y ∧ ¬ FigureLinks y) x := by
  rintro ⟨x, link, step⟩
  cases x with
  | root b => exact link
  | link n =>
    have gate := (label_step_link FigureLabel (FigureGate false) (FigureContext true) _ n).mp step
    simp [FigureGate, PropGate, FigureLinks] at gate

theorem figure_and_on_all_on_not_supported :
    ¬ Supported (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) := by
  intro supported
  apply figure_and_on_all_links_unfed
  apply supported FigureLinks
  · intro x hx
    cases x with
    | root b => exact False.elim hx
    | link n => exact True.intro
  · exact ⟨.link 0, True.intro⟩

theorem figure_or_on_all_on_supported :
    Supported (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) := by
  let F := Step (fun _ => True) (LabelDependency FigureLabel)
    (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext true))
  have admissible := label_gate_admissible FigureLabel (FigureGate true)
  have fixed : Fixed F (LabelState (FigureContext true) (fun _ => True)) :=
    (figure_full_or_on _).mpr rfl
  apply (contextual_grounded_fixed_iff_least admissible (label_context_legal FigureLabel (FigureContext true)) fixed).mpr
  have leastFix : Fixed F (Least F) := least_fixed (step_monotone admissible _)
  exact ((figure_full_or_on _).mp leastFix).symm

theorem rootless_all_on_fixed_ungrounded :
    Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism (fun _ => False))
      (fun _ => True) ∧
    ¬ Supported (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism (fun _ => False))
      (fun _ => True) :=
  ⟨(rootless_fixed_iff_constants _).mpr (Or.inr rfl), rootless_all_on_not_supported⟩

theorem figure_and_on_all_on_fixed_ungrounded :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) ∧
    ¬ Supported (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) :=
  ⟨(figure_full_and_on _).mpr (Or.inr rfl), figure_and_on_all_on_not_supported⟩

theorem figure_or_on_all_on_fixed_grounded :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) ∧
    Supported (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext true)))
      (LabelState (FigureContext true) (fun _ => True)) :=
  ⟨(figure_full_or_on _).mpr rfl, figure_or_on_all_on_supported⟩

end DeterminationPatterns
