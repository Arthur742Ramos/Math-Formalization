module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the grounded fixed-point specialization. -/
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

/-- Inclusion of input regions implies inclusion of their images. -/
def Monotone {α : Type u} (F : Region α → Region α) : Prop :=
  ∀ A B, Sub A B → Sub (F A) (F B)

/-- Intersection of all pre-fixed regions of `F`. -/
def Least {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∀ S, Sub (F S) S → S x

/-- Union of all post-fixed regions of `F`. -/
def Greatest {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∃ S, Sub S (F S) ∧ S x

/-- `X` is unchanged by `F`. -/
def Fixed {α : Type u} (F : Region α → Region α) (X : Region α) : Prop := F X = X


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


/-- Every nonempty subset `S` of `X` intersects the image under `F`
of `X` with `S` removed. -/
def Supported {α : Type u} (F : Region α → Region α) (X : Region α) : Prop :=
  ∀ S : Region α, Sub S X → (∃ x, S x) →
    ∃ x, S x ∧ F (fun y => X y ∧ ¬ S y) x

/-- The grounded fixed-point equivalence for a monotone powerset map,
following Bogaerts, Vennekens and Denecker, Artificial Intelligence 224
(2015), Proposition 3.10 and the powerset discussion. This is an established
theorem, not a new general result. -/
theorem supported_fixed_iff_least {α : Type u} {F : Region α → Region α}
    (hm : Monotone F) {X : Region α} (hX : Fixed F X) :
    Supported F X ↔ X = Least F := by
  classical
  have low : Sub (Least F) X := (fixed_bounds hX).1
  have leastFix : Fixed F (Least F) := least_fixed hm
  constructor
  · intro hs
    apply funext
    intro x
    apply propext
    constructor
    · intro hx
      apply Classical.byContradiction; intro hn
      let S : Region α := fun y => X y ∧ ¬ Least F y
      have ssub : Sub S X := by intro y hy; exact hy.1
      obtain ⟨y, ⟨hyX, hyNot⟩, hFy⟩ := hs S ssub ⟨x, hx, hn⟩
      have remain : Sub (fun y => X y ∧ ¬ S y) (Least F) := by
        intro z hz
        apply Classical.byContradiction; intro hzNot
        exact hz.2 ⟨hz.1, hzNot⟩
      have hlow : F (Least F) y := hm _ _ remain hFy
      rw [leastFix] at hlow
      exact hyNot hlow
    · intro hl; exact low hl
  · intro hEq S hSX hS
    obtain ⟨x, hx⟩ := hS
    apply Classical.byContradiction; intro hNone
    have pre : Sub (F (fun y => X y ∧ ¬ S y)) (fun y => X y ∧ ¬ S y) := by
      intro y hy
      have hxy : X y := by
        have hsub : Sub (fun y => X y ∧ ¬ S y) X := by intro z hz; exact hz.1
        have hf : F X y := hm _ _ hsub hy
        rw [hX] at hf
        exact hf
      have hn : ¬ S y := by
        intro hsy
        exact hNone ⟨y, hsy, hy⟩
      exact ⟨hxy, hn⟩
    have hxLeast : Least F x := by rw [← hEq]; exact hSX hx
    have hxNot : ¬ S x := (least_le F _ pre hxLeast).2
    exact hxNot hx


/-- At any legal root context, a fixed solution satisfies the removed-portion groundedness condition exactly when it is least. -/
theorem contextual_grounded_fixed_iff_least {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} {U X : Region α}
    (h : Mechanism C D f) (_hU : Sub U (Roots C D))
    (hX : Fixed (Step C D f U) X) :
    Supported (Step C D f U) X ↔ X = Least (Step C D f U) :=
  supported_fixed_iff_least (step_monotone h U) hX

end DeterminationPatterns
