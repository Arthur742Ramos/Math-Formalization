module
public import DeterminationPatterns.SharedSpine
@[expose] public section
namespace DeterminationPatterns
universe u

def DependencyAncestor {α : Type u} (C : Region α) (D : α → α → Prop) (b x : α) : Prop :=
  C b ∧ C x ∧ FiniteClosure (RestrictedEdge C D) b x

def FirstMember {α : Type u} (C : Region α) (D : α → α → Prop) (b x : α) : Prop :=
  DependencyAncestor C D b x ∧ Roots C D b

def Grounded {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) : Prop :=
  C x ∧ ∃ y, C y ∧ D y x

def LiteralLocalFoundation {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → Grounded C D x → ∃ b, FirstMember C D b x

theorem root_reachable_iff_first_member {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) :
    RootReachable C D x ↔ ∃ b, FirstMember C D b x := by
  unfold RootReachable
  rw [internal_reach_source_form]
  constructor
  · rintro ⟨hx, b, hb, hp⟩
    exact ⟨b, ⟨hb.1, hx, hp⟩, hb⟩
  · rintro ⟨b, ⟨_, hx, hp⟩, hb⟩
    exact ⟨hx, b, hb, hp⟩

theorem literal_local_foundation_iff {α : Type u} (C : Region α) (D : α → α → Prop) :
    LiteralLocalFoundation C D ↔ LocalFoundation C D := by
  constructor
  · intro h x hx ⟨y, hyC, hyD⟩
    exact (root_reachable_iff_first_member C D x).mpr (h x hx ⟨hx, y, hyC, hyD⟩)
  · intro h x hx ⟨_, y, hyC, hyD⟩
    exact (root_reachable_iff_first_member C D x).mp (h x hx ⟨y, hyC, hyD⟩)

theorem well_founded_on_iff_restricted_relation {α : Type u} (C : Region α)
    (D : α → α → Prop) : WellFoundedOn C D ↔ WellFounded (RestrictedEdge C D) := by
  constructor
  · intro h
    constructor
    intro x
    by_cases hc : C x
    · exact h x hc
    · apply Acc.intro x
      intro y edge
      exact False.elim (hc edge.2.1)
  · intro h x _
    exact h.apply x

/-- Exactly n edges of the restricted relation. -/
inductive EdgePower {α : Type u} (r : α → α → Prop) : Nat → α → α → Prop where
  | zero (x : α) : EdgePower r 0 x x
  | step {n b y x} : EdgePower r n b y → r y x → EdgePower r (n+1) b x

theorem root_length_iff_edge_power {α : Type u} (C : Region α) (D : α → α → Prop)
    (n : Nat) (x : α) : RootLength C D n x ↔
      ∃ b, Roots C D b ∧ EdgePower (RestrictedEdge C D) n b x := by
  constructor
  · intro h
    induction h with
    | root b hr => exact ⟨b, hr, EdgePower.zero b⟩
    | step p hx edge ih =>
      obtain ⟨b, hb, hp⟩ := ih
      exact ⟨b, hb, EdgePower.step hp ⟨length_carrier p, hx, edge⟩⟩
  · rintro ⟨b, hb, hp⟩
    induction hp with
    | zero => exact RootLength.root _ hb
    | step _ edge ih => exact RootLength.step (ih hb) edge.2.1 edge.2.2

end DeterminationPatterns
