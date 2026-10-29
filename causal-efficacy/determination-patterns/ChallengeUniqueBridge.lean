module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the fixed-point uniqueness and accessibility bridges. -/
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


/-- The least region together with carrier vertices outside the greatest
region; for a legal contextual step of an admissible mechanism this expresses
agreement across all fixed solutions. -/
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


/-- At a carrier vertex, determination is agreement across all fixed solutions. -/
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


theorem contextual_fixed_carrier {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) : Sub X C := by
  intro x hx
  have hf : Step C D f U X x := by rw [fixed]; exact hx
  rcases hf with hu | ⟨hc, _, _⟩
  · exact (ctx hu).1
  · exact hc


/-- The operator has exactly one fixed region. -/
def UniqueFixed {α : Type u} (F : Region α → Region α) : Prop :=
  ∃ X, Fixed F X ∧ ∀ Y, Fixed F Y → Y = X


/-- Dependency edges whose endpoints both lie in `A`. -/
def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x


/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x


/-- Every carrier vertex is accessible for the carrier-restricted dependency relation. -/
def WellFoundedOn {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → Acc (RestrictedEdge C D) x

/-- All carrier vertices are accessible exactly when the carrier-restricted
relation is well founded. -/
theorem accessible_carrier_iff_well_founded {α : Type u} (C : Region α) (D : α → α → Prop) :
    Sub C (AccessibleRegion C D) ↔ WellFoundedOn C D := by
  constructor
  · intro h x hx; exact (h hx).2
  · intro h x hx; exact ⟨hx, h x hx⟩

/-- At a legal context, every carrier vertex is determined exactly when the
contextual operator has a unique fixed solution. -/
theorem whole_determined_iff_unique {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    Sub C (Determined C (Step C D f U)) ↔ UniqueFixed (Step C D f U) := by
  constructor
  · intro determined
    obtain ⟨X, _, fixed⟩ := contextual_solution_exists adm ctx
    refine ⟨X, fixed, ?_⟩
    intro Y fixedY
    have xc := contextual_fixed_carrier ctx fixed
    have yc := contextual_fixed_carrier ctx fixedY
    funext x
    apply propext
    by_cases hc : C x
    · exact (determined_iff_fixed_agreement adm ctx hc).mp (determined hc) Y X fixedY fixed
    · exact ⟨fun hy => False.elim (hc (yc hy)), fun hx => False.elim (hc (xc hx))⟩
  · rintro ⟨X, fixed, unique⟩ x hx
    apply (determined_iff_fixed_agreement adm ctx hx).mpr
    intro Y Z fixedY fixedZ
    rw [unique Y fixedY, unique Z fixedZ]


/-- The carrier-accessibility condition is equivalent to Lean well-foundedness
of the full restricted relation, whose outside vertices have no predecessors. -/
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


end DeterminationPatterns
