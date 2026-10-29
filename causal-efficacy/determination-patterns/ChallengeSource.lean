module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the active determined source inference. -/
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

end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- A finite path whose vertices all belong to A, including its endpoints. -/
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

theorem contextual_least_internal_paths {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} {U : Region α} (adm : Mechanism C D f)
    (_ctx : Sub U (Roots C D)) :
    InternalReach (Least (Step C D f U)) D U = Least (Step C D f U) := by
  classical
  let F := Step C D f U
  let L := Least F
  let R := InternalReach L D U
  have lm : Monotone F := step_monotone adm U
  have lf : Fixed F L := least_fixed lm
  have rl : Sub R L := by
    intro x h
    rcases h with ⟨b, hb, hp⟩
    exact path_target hp
  have ul : Sub U L := by
    intro x hu
    have hf : F L x := Or.inl hu
    rw [lf] at hf
    exact hf
  have pre : Sub (F R) R := by
    intro x hx
    have hxl : L x := by
      have : F L x := lm R L rl hx
      rw [lf] at this
      exact this
    rcases hx with hu | ⟨hc, ⟨p, hp⟩, hf⟩
    · exact ⟨x, hu, InternalPath.refl x hxl⟩
    · have parent : ∃ y, R y ∧ Parents C D x y := by
        apply Classical.byContradiction
        intro hn
        have eq : (fun y => R y ∧ Parents C D x y) = (fun _ => False) := by
          funext y
          apply propext
          constructor
          · intro hy; exact hn ⟨y, hy⟩
          · intro hy; exact False.elim hy
        have hf0 : f x (fun _ => False) := by rw [← eq]; exact hf
        have noParents := (adm x hc).2.1.mp hf0
        exact noParents p hp
      obtain ⟨y, ⟨b, hb, path⟩, hyP⟩ := parent
      exact ⟨b, hb, InternalPath.step path hxl hyP.2⟩
  apply funext
  intro x
  exact propext ⟨fun hx => rl hx, fun hx => least_le F R pre hx⟩

theorem active_determinate_is_least {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} {U X : Region α} {a : α}
    (_adm : Mechanism C D f) (_ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) (active : X a)
    (det : Determined C (Step C D f U) a) : Least (Step C D f U) a := by
  rcases det with hl | ⟨_, hnot⟩
  · exact hl
  · exact False.elim (hnot ((fixed_bounds fixed).2 active))

/-- An active, determinate vertex in a solution has an internal path from an
active root, wholly within the least solution. -/
theorem active_determinate_internal_root_path {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} {U X : Region α} {a : α}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) (active : X a)
    (det : Determined C (Step C D f U) a) :
    InternalReach (Least (Step C D f U)) D U a := by
  rw [contextual_least_internal_paths adm ctx]
  exact active_determinate_is_least adm ctx fixed active det


end DeterminationPatterns

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
