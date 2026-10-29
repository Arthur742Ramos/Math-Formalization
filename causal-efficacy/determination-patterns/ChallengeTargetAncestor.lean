module
import Init
@[expose] public section

/-! Target accessibility and well-foundedness of the ancestor cone. -/
namespace DeterminationPatterns
universe u

/-- A region is a predicate on the ambient type. -/
abbrev Region (α : Type u) := α → Prop

/-- Every member of `A` is a member of `B`. -/
def Sub {α : Type u} (A B : Region α) : Prop := ∀ ⦃x⦄, A x → B x


/-- Finite dependency paths whose endpoints and intermediate vertices lie in A. -/
inductive InternalPath {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop where
  | refl (x : α) : A x → InternalPath A D x x
  | step {b y x : α} : InternalPath A D b y → A x → D y x → InternalPath A D b x


theorem path_target {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (h : InternalPath A D b x) : A x := by
  induction h with
  | refl hx => exact hx
  | step _ hx _ _ => exact hx


theorem path_source {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (h : InternalPath A D b x) : A b := by
  induction h with
  | refl hx => exact hx
  | step _ _ _ ih => exact ih


/-- Dependency edges with both endpoints inside the given region. -/
def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x


/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x


/-- Every carrier vertex is accessible for the carrier-restricted dependency relation. -/
def WellFoundedOn {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → Acc (RestrictedEdge C D) x


/-- Carrier vertices connected by a finite internal path to a target. -/
def AncestorCone {α : Type u} (C T : Region α) (D : α → α → Prop) : Region α :=
  fun x => ∃ t, T t ∧ InternalPath C D x t


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


end DeterminationPatterns
