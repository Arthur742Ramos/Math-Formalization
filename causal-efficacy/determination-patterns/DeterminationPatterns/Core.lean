module
import Init
@[expose] public section

/-! Preliminary semantic infrastructure. This is not a paper theorem package. -/
namespace DeterminationPatterns
universe u
abbrev Region (α : Type u) := α → Prop

def Sub {α : Type u} (A B : Region α) : Prop := ∀ ⦃x⦄, A x → B x

def Parents {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) : Region α :=
  fun y => C y ∧ D y x

def Roots {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ ∀ y, ¬ Parents C D x y

def Mechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x →
    (∀ A B, Sub A B → f x A → f x B) ∧
    (f x (fun _ => False) ↔ ∀ y, ¬ Parents C D x y) ∧
    f x (Parents C D x)

def Relevant {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x → ∀ y, Parents C D x y →
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ f x S ∧ f x (fun z => z = y ∨ S z)

def Step {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U X : Region α) : Region α :=
  fun x => U x ∨ (C x ∧ (∃ y, Parents C D x y) ∧
    f x (fun y => X y ∧ Parents C D x y))

def Monotone {α : Type u} (F : Region α → Region α) : Prop :=
  ∀ A B, Sub A B → Sub (F A) (F B)

def Least {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∀ S, Sub (F S) S → S x

def Greatest {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∃ S, Sub S (F S) ∧ S x

def Fixed {α : Type u} (F : Region α → Region α) (X : Region α) : Prop := F X = X

def Determined {α : Type u} (C : Region α) (F : Region α → Region α) : Region α :=
  fun x => Least F x ∨ (C x ∧ ¬ Greatest F x)

theorem step_monotone {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (h : Mechanism C D f) (U : Region α) :
    Monotone (Step C D f U) := by
  intro A B hAB x hx
  rcases hx with hu | ⟨hc, hp, hf⟩
  · exact Or.inl hu
  · exact Or.inr ⟨hc, hp, (h x hc).1 _ _ (fun _ hz => ⟨hAB hz.1, hz.2⟩) hf⟩

theorem least_le {α : Type u} (F : Region α → Region α) (S : Region α)
    (h : Sub (F S) S) : Sub (Least F) S := by
  intro x hx
  exact hx S h

theorem le_greatest {α : Type u} (F : Region α → Region α) (S : Region α)
    (h : Sub S (F S)) : Sub S (Greatest F) := by
  intro x hx
  exact ⟨S, h, hx⟩

theorem least_fixed {α : Type u} {F : Region α → Region α} (h : Monotone F) :
    Fixed F (Least F) := by
  have pre : Sub (F (Least F)) (Least F) := by
    intro x hx S hS
    exact hS (h (Least F) S (least_le F S hS) hx)
  have post : Sub (Least F) (F (Least F)) :=
    least_le F (F (Least F)) (h _ _ pre)
  apply funext
  intro x
  exact propext ⟨fun hx => pre hx, fun hx => post hx⟩

theorem greatest_fixed {α : Type u} {F : Region α → Region α} (h : Monotone F) :
    Fixed F (Greatest F) := by
  have post : Sub (Greatest F) (F (Greatest F)) := by
    intro x hx
    rcases hx with ⟨S, hS, hsx⟩
    exact h S (Greatest F) (le_greatest F S hS) (hS hsx)
  have pre : Sub (F (Greatest F)) (Greatest F) :=
    le_greatest F (F (Greatest F)) (h _ _ post)
  apply funext
  intro x
  exact propext ⟨fun hx => pre hx, fun hx => post hx⟩

theorem fixed_bounds {α : Type u} {F : Region α → Region α} {X : Region α}
    (hx : Fixed F X) : Sub (Least F) X ∧ Sub X (Greatest F) := by
  have pre : Sub (F X) X := by intro x h; rw [hx] at h; exact h
  have post : Sub X (F X) := by intro x h; rw [hx]; exact h
  exact ⟨least_le F X pre, le_greatest F X post⟩

theorem contextual_solution_exists {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} {U : Region α} (h : Mechanism C D f)
    (hU : Sub U (Roots C D)) :
    ∃ X : Region α, Sub X C ∧ Fixed (Step C D f U) X := by
  refine ⟨Least (Step C D f U), ?_, least_fixed (step_monotone h U)⟩
  apply least_le
  intro x hx
  rcases hx with hu | ⟨hc, _, _⟩
  · exact (hU hu).1
  · exact hc

theorem determined_iff_fixed_agreement {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} {U : Region α} {x : α}
    (h : Mechanism C D f) (_hU : Sub U (Roots C D)) (hx : C x) :
    Determined C (Step C D f U) x ↔
      ∀ X Y, Fixed (Step C D f U) X → Fixed (Step C D f U) Y → (X x ↔ Y x) := by
  classical
  let F := Step C D f U
  have hm : Monotone F := step_monotone h U
  constructor
  · intro hd X Y hX hY
    have bx := fixed_bounds hX
    have by' := fixed_bounds hY
    rcases hd with hl | ⟨_, hn⟩
    · exact ⟨fun _ => by'.1 hl, fun _ => bx.1 hl⟩
    · exact ⟨fun hxx => False.elim (hn (bx.2 hxx)),
        fun hyy => False.elim (hn (by'.2 hyy))⟩
  · intro ha
    have hagree := ha (Least F) (Greatest F) (least_fixed hm) (greatest_fixed hm)
    by_cases hl : Least F x
    · exact Or.inl hl
    · exact Or.inr ⟨hx, fun hg => hl (hagree.mpr hg)⟩

end DeterminationPatterns
