module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the unrestricted uniform synthesis. -/
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


/-- The operator has a fixed region and every fixed region equals it. -/
def UniqueFixed {α : Type u} (F : Region α → Region α) : Prop :=
  ∃ X, Fixed F X ∧ ∀ Y, Fixed F Y → Y = X

/-- One mechanism has a unique fixed solution at every legal root context. -/
def ContextDeterminate {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ U, Sub U (Roots C D) → UniqueFixed (Step C D f U)


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

/-- Finite reachability from carrier roots. -/
def RootReachable {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  InternalReach C D (Roots C D)

theorem contextual_fixed_carrier {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) : Sub X C := by
  intro x hx
  have hf : Step C D f U X x := by rw [fixed]; exact hx
  rcases hf with hu | ⟨hc, _, _⟩
  · exact (ctx hu).1
  · exact hc

theorem contextual_fixed_roots {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (_ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) :
    ∀ x, Roots C D x → (X x ↔ U x) := by
  intro x root
  constructor
  · intro hx
    have hf : Step C D f U X x := by rw [fixed]; exact hx
    rcases hf with hu | ⟨_, ⟨y, hy⟩, _⟩
    · exact hu
    · exact False.elim (root.2 y hy)
  · intro hu
    have hf : Step C D f U X x := Or.inl hu
    rw [fixed] at hf
    exact hf

/-- Every carrier vertex with a carrier parent has a finite carrier-internal
path from a carrier root. -/
def LocalFoundation {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → (∃ y, Parents C D x y) → RootReachable C D x

theorem local_foundation_iff_all_reachable {α : Type u} (C : Region α) (D : α → α → Prop) :
    LocalFoundation C D ↔ Sub C (RootReachable C D) := by
  classical
  constructor
  · intro foundation x hx
    by_cases hparent : ∃ y, Parents C D x y
    · exact foundation x hx hparent
    · have root : Roots C D x := ⟨hx, fun y hy => hparent ⟨y, hy⟩⟩
      exact ⟨x, root, InternalPath.refl x hx⟩
  · intro h x hx _
    exact h hx

/-- Finite root-to-node paths indexed by their number of edges. -/
inductive RootLength {α : Type u} (C : Region α) (D : α → α → Prop) : Nat → α → Prop where
  | root (x : α) : Roots C D x → RootLength C D 0 x
  | step {n y x} : RootLength C D n y → C x → D y x → RootLength C D (n+1) x

theorem reachable_has_length {α : Type u} {C : Region α} {D : α → α → Prop}
    {x : α} (h : RootReachable C D x) : ∃ n, RootLength C D n x := by
  obtain ⟨b, hb, hp⟩ := h
  induction hp with
  | refl _ => exact ⟨0, RootLength.root b hb⟩
  | step path hx edge ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, RootLength.step hn hx edge⟩

theorem length_carrier {α : Type u} {C : Region α} {D : α → α → Prop}
    {n : Nat} {x : α} (h : RootLength C D n x) : C x := by
  cases h with
  | root _ hr => exact hr.1
  | step _ hc _ => exact hc

theorem exists_min_nat (P : Nat → Prop) (existsP : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  classical
  obtain ⟨n, hn⟩ := existsP
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hm⟩ := smaller
      exact ih m hmn hm
    · exact ⟨n, hn, fun m hmn hm => smaller ⟨m, hmn, hm⟩⟩

/-- The shortest finite root distance when one exists; a fallback is used otherwise. -/
noncomputable def RootRank {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) : Nat := by
  classical
  exact if h : ∃ n, RootLength C D n x then Classical.choose (exists_min_nat _ h) else 0

theorem root_rank_spec {α : Type u} {C : Region α} {D : α → α → Prop} {x : α}
    (h : ∃ n, RootLength C D n x) :
    RootLength C D (RootRank C D x) x ∧
      ∀ m, m < RootRank C D x → ¬ RootLength C D m x := by
  classical
  simpa [RootRank, h] using Classical.choose_spec (exists_min_nat (fun n => RootLength C D n x) h)

theorem nonroot_length_predecessor {α : Type u} {C : Region α} {D : α → α → Prop}
    {n : Nat} {x : α} (path : RootLength C D n x) (notRoot : ¬ Roots C D x) :
    ∃ y m, Parents C D x y ∧ n = m + 1 ∧ RootLength C D m y := by
  cases path with
  | root _ hr => exact False.elim (notRoot hr)
  | @step m y x path hx edge =>
    exact ⟨y, m, ⟨length_carrier path, edge⟩, rfl, path⟩

theorem ranked_parent_exists {α : Type u} {C : Region α} {D : α → α → Prop} {x : α}
    (reach : RootReachable C D x) (notRoot : ¬ Roots C D x) :
    ∃ y, Parents C D x y ∧ RootRank C D y < RootRank C D x := by
  have spec := root_rank_spec (reachable_has_length reach)
  obtain ⟨y, n, hp, heq, path⟩ := nonroot_length_predecessor spec.1 notRoot
  have yspec := root_rank_spec ⟨n, path⟩
  have hnot : ¬ n < RootRank C D y := by
    intro hlt
    exact yspec.2 n hlt path
  have hle : RootRank C D y ≤ n := Nat.le_of_not_gt hnot
  rw [heq]
  exact ⟨y, hp, Nat.lt_succ_of_le hle⟩

/-- At each nonroot copy a classically chosen parent of smaller root rank;
roots have a canonical true entry. -/
noncomputable def ForestMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (x : α) (S : Region α) : Prop := by
  classical
  exact if Roots C D x then True
    else if h : ∃ y, Parents C D x y ∧ RootRank C D y < RootRank C D x
      then S (Classical.choose h) else False

theorem forest_mechanism_admissible {α : Type u} {C : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) : Mechanism C D (ForestMechanism C D) := by
  classical
  intro x hx
  by_cases hr : Roots C D x
  · simp [ForestMechanism, hr, hr.2]
  · have hp := ranked_parent_exists (reach hx) hr
    simp only [ForestMechanism, hr, hp, ↓reduceIte, ↓reduceDIte]
    have chosen := Classical.choose_spec hp
    constructor
    · intro A B hAB h
      exact hAB h
    constructor
    · constructor
      · intro h; exact False.elim h
      · intro h; exact False.elim (h _ chosen.1)
    · exact chosen.1

theorem forest_solutions_equal {α : Type u} {C U X Y : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) (ctx : Sub U (Roots C D))
    (fixedX : Fixed (Step C D (ForestMechanism C D) U) X)
    (fixedY : Fixed (Step C D (ForestMechanism C D) U) Y) : X = Y := by
  classical
  have xc : Sub X C := contextual_fixed_carrier ctx fixedX
  have yc : Sub Y C := contextual_fixed_carrier ctx fixedY
  have agree : ∀ n : Nat, ∀ x, C x → RootRank C D x = n → (X x ↔ Y x) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxC heq
      by_cases root : Roots C D x
      · exact (contextual_fixed_roots ctx fixedX x root).trans
          (contextual_fixed_roots ctx fixedY x root).symm
      · have hp := ranked_parent_exists (reach hxC) root
        let y := Classical.choose hp
        have hy := Classical.choose_spec hp
        have hlt : RootRank C D y < n := by rw [← heq]; exact hy.2
        have xy : X y ↔ Y y := ih (RootRank C D y) hlt y hy.1.1 rfl
        have notU : ¬ U x := fun hu => root (ctx hu)
        have xeq : X x ↔ X y := by
          constructor
          · intro hx
            have h : Step C D (ForestMechanism C D) U X x := by rw [fixedX]; exact hx
            rcases h with hu | ⟨_, _, gate⟩
            · exact False.elim (notU hu)
            · simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte] at gate
              exact gate.1
          · intro hyX
            have h : Step C D (ForestMechanism C D) U X x := by
              apply Or.inr
              refine ⟨hxC, ⟨y, hy.1⟩, ?_⟩
              simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte]
              exact ⟨hyX, hy.1⟩
            rw [fixedX] at h
            exact h
        have yeq : Y x ↔ Y y := by
          constructor
          · intro hx
            have h : Step C D (ForestMechanism C D) U Y x := by rw [fixedY]; exact hx
            rcases h with hu | ⟨_, _, gate⟩
            · exact False.elim (notU hu)
            · simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte] at gate
              exact gate.1
          · intro hyY
            have h : Step C D (ForestMechanism C D) U Y x := by
              apply Or.inr
              refine ⟨hxC, ⟨y, hy.1⟩, ?_⟩
              simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte]
              exact ⟨hyY, hy.1⟩
            rw [fixedY] at h
            exact h
        exact xeq.trans (xy.trans yeq.symm)
  funext x
  apply propext
  by_cases hc : C x
  · exact agree (RootRank C D x) x hc rfl
  · exact ⟨fun hx => False.elim (hc (xc hx)), fun hy => False.elim (hc (yc hy))⟩

theorem forest_copy_every_context_unique {α : Type u} {C : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) : ContextDeterminate C D (ForestMechanism C D) := by
  intro U ctx
  have adm := forest_mechanism_admissible reach
  obtain ⟨X, _, fixed⟩ := contextual_solution_exists adm ctx
  refine ⟨X, fixed, ?_⟩
  intro Y fixedY
  exact forest_solutions_equal reach ctx fixedY fixed


/-- One admissible mechanism works at every legal root context exactly when
all carrier vertices have finite root ancestry. Full edge relevance is not assumed. -/
theorem some_mechanism_every_context_unique_iff_local_foundation {α : Type u}
    (C : Region α) (D : α → α → Prop) :
    (∃ f, Mechanism C D f ∧ ContextDeterminate C D f) ↔ LocalFoundation C D := by
  classical
  constructor
  · rintro ⟨f, adm, all⟩
    apply (local_foundation_iff_all_reachable C D).mpr
    let U : Region α := fun _ => False
    let F := Step C D f U
    let X : Region α := fun x => C x ∧ ¬ RootReachable C D x
    have ctx : Sub U (Roots C D) := by intro x h; exact False.elim h
    have emptyFix : Fixed F U := by
      funext x
      apply propext
      constructor
      · intro h
        rcases h with hu | ⟨hc, hp, hf⟩
        · exact hu
        · have emptyInput : (fun y => U y ∧ Parents C D x y) = (fun _ => False) := by
            funext y
            exact propext ⟨fun h => h.1, fun h => False.elim h⟩
          rw [emptyInput] at hf
          obtain ⟨y, hy⟩ := hp
          exact ((adm x hc).2.1.mp hf y) hy
      · intro h; exact False.elim h
    have post : Sub X (F X) := by
      intro x ⟨hc, hnR⟩
      have hp : ∃ y, Parents C D x y := by
        apply Classical.byContradiction
        intro no
        apply hnR
        have root : Roots C D x := ⟨hc, fun y hy => no ⟨y, hy⟩⟩
        exact ⟨x, root, InternalPath.refl x hc⟩
      have parentNotReach : ∀ y, Parents C D x y → ¬ RootReachable C D y := by
        intro y hy ⟨b, hb, path⟩
        apply hnR
        exact ⟨b, hb, InternalPath.step path hc hy.2⟩
      have input : (fun y => X y ∧ Parents C D x y) = Parents C D x := by
        funext y
        apply propext
        constructor
        · exact fun h => h.2
        · intro hy
          exact ⟨⟨hy.1, parentNotReach y hy⟩, hy⟩
      right
      refine ⟨hc, hp, ?_⟩
      rw [input]
      exact (adm x hc).2.2
    obtain ⟨Y, _, unique⟩ := all U ctx
    have eq : Greatest F = U :=
      (unique (Greatest F) (greatest_fixed (step_monotone adm U))).trans
        (unique U emptyFix).symm
    intro x hc
    apply Classical.byContradiction
    intro hnR
    have hx : Greatest F x := le_greatest F X post ⟨hc, hnR⟩
    rw [eq] at hx
    exact hx
  · intro foundation
    have reach := (local_foundation_iff_all_reachable C D).mp foundation
    exact ⟨ForestMechanism C D, forest_mechanism_admissible reach,
      forest_copy_every_context_unique reach⟩

end DeterminationPatterns
