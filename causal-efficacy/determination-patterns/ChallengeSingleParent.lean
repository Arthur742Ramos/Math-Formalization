module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the single-parent reachability and copying. -/
namespace DeterminationPatterns
universe u
/-- A region is a predicate on the ambient type; the carrier may be any region. -/
abbrev Region (α : Type u) := α → Prop

/-- Every member of `A` is a member of `B`. -/
def Sub {α : Type u} (A B : Region α) : Prop := ∀ ⦃x⦄, A x → B x

/-- Carrier vertices with an incoming dependency edge to `x`. -/
def Parents {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) : Region α :=
  fun y => C y ∧ D y x

/-- Carrier vertices having no carrier parent. -/
def Roots {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ ∀ y, ¬ Parents C D x y

/-- At each carrier vertex the mechanism is monotone on all input regions,
returns true on empty input exactly at roots, and returns true on all parents. -/
def Mechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x →
    (∀ A B, Sub A B → f x A → f x B) ∧
    (f x (fun _ => False) ↔ ∀ y, ¬ Parents C D x y) ∧
    f x (Parents C D x)

/-- The contextual update includes every element of `U` and evaluates each
non-root carrier vertex on its currently active parents. If `U` is contained
in the roots, it selects the roots that are turned on. -/
def Step {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U X : Region α) : Region α :=
  fun x => U x ∨ (C x ∧ (∃ y, Parents C D x y) ∧
    f x (fun y => X y ∧ Parents C D x y))

/-- Finite dependency paths whose endpoints and intermediate vertices lie in A. -/
inductive InternalPath {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop where
  | refl (x : α) : A x → InternalPath A D x x
  | step {b y x : α} : InternalPath A D b y → A x → D y x → InternalPath A D b x

/-- Reachability from `B` along finite paths internal to `A`, including both endpoints. -/
def InternalReach {α : Type u} (A : Region α) (D : α → α → Prop)
    (B : Region α) : Region α := fun x => ∃ b, B b ∧ InternalPath A D b x

theorem path_target {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (h : InternalPath A D b x) : A x := by
  induction h with
  | refl hx => exact hx
  | step _ hx _ _ => exact hx


/-- Dependency edges with both endpoints inside the given region. -/
def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x

/-- Finite reachability from carrier roots. -/
def RootReachable {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  InternalReach C D (Roots C D)

/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x


/-- Each carrier vertex has at most one carrier parent. -/
def SingleParent {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → ∀ y z, Parents C D x y → Parents C D x z → y = z


theorem accessible_reachable_direct {α : Type u} {C : Region α} {D : α → α → Prop}
    {x : α} (hx : AccessibleRegion C D x) : RootReachable C D x := by
  classical
  rcases hx with ⟨hc, ha⟩
  induction ha with
  | intro x hacc ih =>
    by_cases hp : ∃ y, Parents C D x y
    · obtain ⟨y, hy⟩ := hp
      obtain ⟨b, hb, path⟩ := ih y ⟨hy.1, hc, hy.2⟩ hy.1
      exact ⟨b, hb, InternalPath.step path hc hy.2⟩
    · exact ⟨x, ⟨hc, fun y hy => hp ⟨y, hy⟩⟩, InternalPath.refl x hc⟩

theorem single_parent_accessible_iff_reachable {α : Type u} {C : Region α}
    {D : α → α → Prop} (single : SingleParent C D) :
    AccessibleRegion C D = RootReachable C D := by
  funext x
  apply propext
  constructor
  · intro hx
    exact accessible_reachable_direct hx
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
