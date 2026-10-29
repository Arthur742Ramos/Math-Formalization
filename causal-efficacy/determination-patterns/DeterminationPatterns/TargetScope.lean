module
public import DeterminationPatterns.SourceSemantics
@[expose] public section
namespace DeterminationPatterns
universe u

/-- Vertices connected to a target by a finite path entirely in the carrier. -/
def AncestorCone {α : Type u} (C T : Region α) (D : α → α → Prop) : Region α :=
  fun x => ∃ t, T t ∧ InternalPath C D x t

/-- Each carrier vertex has at most one carrier parent. -/
def SingleParent {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → ∀ y z, Parents C D x y → Parents C D x z → y = z

theorem prepend_internal_path {α : Type u} {C : Region α} {D : α → α → Prop}
    {p x t : α} (hp : C p) (edge : D p x) (path : InternalPath C D x t) :
    InternalPath C D p t := by
  induction path with
  | refl hx => exact InternalPath.step (InternalPath.refl p hp) hx edge
  | step path hx d ih => exact InternalPath.step ih hx d

theorem cone_subset_carrier {α : Type u} {C T : Region α} {D : α → α → Prop} :
    Sub (AncestorCone C T D) C := by
  intro x ⟨t, _, path⟩
  exact path_source path

theorem cone_parent_closed {α : Type u} {C T : Region α} {D : α → α → Prop}
    {x y : α} (hx : AncestorCone C T D x) (hy : C y) (edge : D y x) :
    AncestorCone C T D y := by
  obtain ⟨t, ht, path⟩ := hx
  exact ⟨t, ht, prepend_internal_path hy edge path⟩

theorem acc_carrier_to_cone {α : Type u} {C T : Region α} {D : α → α → Prop}
    {x : α} (ha : Acc (RestrictedEdge C D) x) :
    Acc (RestrictedEdge (AncestorCone C T D) D) x := by
  induction ha with
  | intro x next ih =>
    apply Acc.intro
    intro y hy
    exact ih y ⟨cone_subset_carrier hy.1, cone_subset_carrier hy.2.1, hy.2.2⟩

theorem acc_cone_to_carrier {α : Type u} {C T : Region α} {D : α → α → Prop}
    {x : α} (ha : Acc (RestrictedEdge (AncestorCone C T D) D) x)
    (hx : AncestorCone C T D x) : Acc (RestrictedEdge C D) x := by
  induction ha with
  | intro x next ih =>
    apply Acc.intro
    intro y hy
    have hycone := cone_parent_closed hx hy.1 hy.2.2
    exact ih y ⟨hycone, hx, hy.2.2⟩ hycone

theorem internal_path_acc_predecessor {α : Type u} {C : Region α} {D : α → α → Prop}
    {x t : α} (path : InternalPath C D x t) (ha : Acc (RestrictedEdge C D) t) :
    Acc (RestrictedEdge C D) x := by
  induction path with
  | refl => exact ha
  | step path hx edge ih =>
    apply ih
    exact ha.inv ⟨path_target path, hx, edge⟩

/-- A target is accessible exactly when the dependency relation on all its
carrier-internal ancestors is well founded. The target may be empty. -/
theorem target_accessibility_iff_ancestor_well_founded {α : Type u}
    {C T : Region α} {D : α → α → Prop} (target : Sub T C) :
    Sub T (AccessibleRegion C D) ↔ WellFoundedOn (AncestorCone C T D) D := by
  constructor
  · intro h x hx
    obtain ⟨t, ht, path⟩ := hx
    exact acc_carrier_to_cone (internal_path_acc_predecessor path (h ht).2)
  · intro wf x hx
    have hc := target hx
    have hcone : AncestorCone C T D x := ⟨x, hx, InternalPath.refl x hc⟩
    exact ⟨hc, acc_cone_to_carrier (wf x hcone) hcone⟩

/-- At most one parent per vertex makes root reachability and accessibility
coincide, including on infinite and empty carriers. -/
theorem single_parent_accessible_iff_reachable {α : Type u} {C : Region α}
    {D : α → α → Prop} (single : SingleParent C D) :
    AccessibleRegion C D = RootReachable C D := by
  funext x
  apply propext
  constructor
  · intro hx
    exact region_subset_reachable (accessible_region_conditions C D) hx
  · rintro ⟨b, hb, path⟩
    have accroot : Acc (RestrictedEdge C D) b := by
      apply Acc.intro
      intro y edge
      exact False.elim (hb.2 y ⟨edge.1, edge.2.2⟩)
    have ha : Acc (RestrictedEdge C D) x := by
      induction path with
      | refl => exact accroot
      | step path hx edge ih =>
        apply Acc.intro
        intro y hy
        have eq : y = _ := single _ hx y _ ⟨hy.1, hy.2.2⟩ ⟨path_target path, edge⟩
        subst y
        exact ih
    exact ⟨path_target path, ha⟩

/-- At a fixed legal context, universal target determination is equivalent to
well-foundedness of the target's ancestor cone. -/
theorem every_context_target_iff_ancestor_well_founded {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (target : Sub T C)
    (ctx : Sub U (Roots C D)) :
    (∀ f, Mechanism C D f → Sub T (Determined C (Step C D f U))) ↔
      WellFoundedOn (AncestorCone C T D) D := by
  rw [every_context_determination_iff_accessible ctx,
    target_accessibility_iff_ancestor_well_founded target]

/-- Under the single-parent assumption, possible and universal target
 determination coincide at each fixed legal context. -/
theorem single_parent_some_iff_every_context_determination {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (single : SingleParent C D)
    (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Sub T (Determined C (Step C D f U))) ↔
      (∀ f, Mechanism C D f → Sub T (Determined C (Step C D f U))) := by
  rw [some_context_determination_iff_reachable ctx,
    every_context_determination_iff_accessible ctx,
    single_parent_accessible_iff_reachable single]


/-- Every admissible mechanism copies the unique parent at a nonroot, in
any legal context. -/
theorem single_parent_step_copies {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} {x y : α}
    (single : SingleParent C D) (adm : Mechanism C D f)
    (ctx : Sub U (Roots C D)) (hc : C x) (hy : Parents C D x y) :
    Step C D f U X x ↔ X y := by
  classical
  have notU : ¬ U x := by
    intro hu
    exact (ctx hu).2 y hy
  by_cases hxy : X y
  · have input : (fun z => X z ∧ Parents C D x z) = Parents C D x := by
      funext z
      apply propext
      constructor
      · exact fun h => h.2
      · intro hz
        have eq := single x hc z y hz hy
        subst z
        exact ⟨hxy, hy⟩
    constructor
    · intro _; exact hxy
    · intro _
      right
      refine ⟨hc, ⟨y, hy⟩, ?_⟩
      rw [input]
      exact (adm x hc).2.2
  · have input : (fun z => X z ∧ Parents C D x z) = (fun _ => False) := by
      funext z
      apply propext
      constructor
      · intro hz
        have eq := single x hc z y hz.2 hy
        subst z
        exact hxy hz.1
      · intro h; exact h.elim
    constructor
    · intro h
      rcases h with hu | ⟨_, _, hf⟩
      · exact False.elim (notU hu)
      · rw [input] at hf
        exact False.elim (((adm x hc).2.1.mp hf y) hy)
    · intro h; exact False.elim (hxy h)

end DeterminationPatterns
