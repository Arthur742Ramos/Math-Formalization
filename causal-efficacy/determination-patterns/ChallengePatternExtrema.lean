module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for extrema of the admissible pattern witness. -/
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

/-- Each carrier edge has a subset of the other parents on which its target
output is false and becomes true when that parent is added. -/
def Relevant {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x → ∀ y, Parents C D x y →
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ f x S ∧ f x (fun z => z = y ∨ S z)

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


/-- The least region and carrier members outside the greatest region. -/
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


/-- The carrier is exactly the disjoint union of L, Z and Q. -/
def StatusPartition {α : Type u} (C L Z Q : Region α) : Prop :=
  (∀ x, C x ↔ L x ∨ Z x ∨ Q x) ∧
  (∀ x, ¬ (L x ∧ Z x)) ∧ (∀ x, ¬ (L x ∧ Q x)) ∧ (∀ x, ¬ (Z x ∧ Q x))

/-- `U` lies in `L` and all roots outside `U` lie in `Z`; `L` is exactly
the set reachable from `U` through `L`, `Z` is exactly the set reachable
from roots outside `U` through `Z`, and every `Q` vertex has a `Q` parent.
The condition that `U` consists of roots is a separate assumption. -/
def PatternConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (U L Z Q : Region α) : Prop :=
  Sub U L ∧ Sub (fun x => Roots C D x ∧ ¬ U x) Z ∧
  InternalReach L D U = L ∧
  InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z ∧
  (∀ x, Q x → ∃ y, Parents C D x y ∧ Q y)

/-- The OR gate on parents, with the empty-parent case set to true. -/
def OrGate {α : Type u} (P S : Region α) : Prop :=
  (∀ y, ¬ P y) ∨ ∃ y, P y ∧ S y

/-- The AND gate on parents, true exactly when all parents are in `S`. -/
def AndGate {α : Type u} (P S : Region α) : Prop := ∀ y, P y → S y

/-- The mixed gate fires on an active `Z` parent, or on an active `Q`
parent together with every `L` parent active. -/
def SplitGate {α : Type u} (P L Z Q S : Region α) : Prop :=
  ((∃ y, P y ∧ Q y ∧ S y) ∧ (∀ y, P y ∧ L y → S y)) ∨
    (∃ y, P y ∧ Z y ∧ S y)

/-- The witness uses OR on L, otherwise AND on Z, and the split gate elsewhere.
Admissibility and relevance are required only at carrier vertices. -/
noncomputable def StatusMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (L Z Q : Region α) (x : α) (S : Region α) : Prop := by
  classical
  exact if L x then OrGate (Parents C D x) S
    else if Z x then AndGate (Parents C D x) S
    else SplitGate (Parents C D x) L Z Q S

theorem path_last_or_seed {α : Type u} {A B : Region α} {D : α → α → Prop}
    {x : α} (h : InternalReach A D B x) :
    B x ∨ ∃ y, A y ∧ D y x := by
  obtain ⟨b, hb, hp⟩ := h
  cases hp with
  | refl _ => exact Or.inl hb
  | step path _ edge => exact Or.inr ⟨_, path_target path, edge⟩

theorem status_two_fixed_points {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) :
    Fixed (Step C D (StatusMechanism C D L Z Q) U) L ∧
    Fixed (Step C D (StatusMechanism C D L Z Q) U) (fun x => C x ∧ ¬ Z x) := by
  classical
  have lc : Sub L C := by intro x hx; exact (part.1 x).mpr (Or.inl hx)
  have zc : Sub Z C := by intro x hx; exact (part.1 x).mpr (Or.inr (Or.inl hx))
  have qc : Sub Q C := by intro x hx; exact (part.1 x).mpr (Or.inr (Or.inr hx))
  have lu : ∀ x, L x → U x ∨ ∃ y, Parents C D x y ∧ L y := by
    intro x hx
    have reach : InternalReach L D U x := by rw [cond.2.2.1]; exact hx
    rcases path_last_or_seed reach with hu | ⟨y, hyL, hD⟩
    · exact Or.inl hu
    · exact Or.inr ⟨y, ⟨lc hyL, hD⟩, hyL⟩
  have zp : ∀ x, Z x → (∀ y, ¬ Parents C D x y) ∨ ∃ y, Parents C D x y ∧ Z y := by
    intro x hx
    have reach : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) x := by
      rw [cond.2.2.2.1]; exact hx
    rcases path_last_or_seed reach with ⟨hroot, _⟩ | ⟨y, hyZ, hD⟩
    · exact Or.inl hroot.2
    · exact Or.inr ⟨y, ⟨zc hyZ, hD⟩, hyZ⟩
  have unotz : ∀ x, U x → ¬ Z x := by
    intro x hu hz
    exact (part.2.1 x) ⟨cond.1 hu, hz⟩
  constructor
  · apply funext
    intro x
    apply propext
    constructor
    · intro h
      rcases h with hu | ⟨hxC, ⟨p, hp⟩, hf⟩
      · exact cond.1 hu
      · by_cases hxL : L x
        · exact hxL
        · by_cases hxZ : Z x
          · simp only [StatusMechanism, hxL, hxZ, ↓reduceIte, AndGate] at hf
            rcases zp x hxZ with hroot | ⟨y, hyP, hyZ⟩
            · exact False.elim (hroot p hp)
            · exact False.elim ((part.2.1 y) ⟨(hf y hyP).1, hyZ⟩)
          · simp only [StatusMechanism, hxL, hxZ, ↓reduceIte, SplitGate] at hf
            rcases hf with ⟨⟨y, _, hyQ, hyL, _⟩, _⟩ | ⟨y, _, hyZ, hyL, _⟩
            · exact False.elim ((part.2.2.1 y) ⟨hyL, hyQ⟩)
            · exact False.elim ((part.2.1 y) ⟨hyL, hyZ⟩)
    · intro hxL
      rcases lu x hxL with hu | ⟨y, hyP, hyL⟩
      · exact Or.inl hu
      · apply Or.inr
        refine ⟨lc hxL, ⟨y, hyP⟩, ?_⟩
        simp only [StatusMechanism, hxL, ↓reduceIte, OrGate]
        exact Or.inr ⟨y, hyP, hyL, hyP⟩
  · apply funext
    intro x
    apply propext
    constructor
    · intro h
      rcases h with hu | ⟨hxC, ⟨p, hp⟩, hf⟩
      · exact ⟨lc (cond.1 hu), unotz x hu⟩
      · refine ⟨hxC, ?_⟩
        intro hxZ
        have hxL : ¬ L x := by intro hl; exact (part.2.1 x) ⟨hl, hxZ⟩
        simp only [StatusMechanism, hxL, hxZ, ↓reduceIte, AndGate] at hf
        rcases zp x hxZ with hroot | ⟨y, hyP, hyZ⟩
        · exact hroot p hp
        · exact (hf y hyP).1.2 hyZ
    · intro ⟨hxC, hxNotZ⟩
      by_cases hxL : L x
      · rcases lu x hxL with hu | ⟨y, hyP, hyL⟩
        · exact Or.inl hu
        · apply Or.inr
          refine ⟨hxC, ⟨y, hyP⟩, ?_⟩
          simp only [StatusMechanism, hxL, ↓reduceIte, OrGate]
          exact Or.inr ⟨y, hyP, ⟨lc hyL, fun hz => (part.2.1 y) ⟨hyL, hz⟩⟩, hyP⟩
      · have hxQ : Q x := by
          rcases (part.1 x).mp hxC with h | h | h
          · exact False.elim (hxL h)
          · exact False.elim (hxNotZ h)
          · exact h
        obtain ⟨q, hqP, hqQ⟩ := cond.2.2.2.2 x hxQ
        apply Or.inr
        refine ⟨hxC, ⟨q, hqP⟩, ?_⟩
        simp only [StatusMechanism, hxL, hxNotZ, ↓reduceIte, SplitGate]
        apply Or.inl
        constructor
        · exact ⟨q, hqP, hqQ, ⟨qc hqQ, fun hz => (part.2.2.2 q) ⟨hz, hqQ⟩⟩, hqP⟩
        · intro y ⟨hyP, hyL⟩
          exact ⟨⟨lc hyL, fun hz => (part.2.1 y) ⟨hyL, hz⟩⟩, hyP⟩

theorem status_forces_paths {α : Type u} {C L Z Q U X : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D (StatusMechanism C D L Z Q) U) X) :
    Sub L X ∧ Sub X (fun x => C x ∧ ¬ Z x) := by
  classical
  let F := Step C D (StatusMechanism C D L Z Q) U
  have fixedF : F X = X := fixed
  have lc : Sub L C := by intro x h; exact (part.1 x).mpr (Or.inl h)
  have zc : Sub Z C := by intro x h; exact (part.1 x).mpr (Or.inr (Or.inl h))
  have ux : Sub U X := by
    intro x hu
    have h : F X x := Or.inl hu
    rw [fixedF] at h
    exact h
  have xc : Sub X C := by
    intro x hx
    have h : F X x := by rw [fixedF]; exact hx
    rcases h with hu | ⟨hc, _, _⟩
    · exact (ctx hu).1
    · exact hc
  have lpath : ∀ x, InternalReach L D U x → X x := by
    intro x h
    obtain ⟨b, hb, path⟩ := h
    induction path with
    | refl _ => exact ux hb
    | @step y x path hxL edge ih =>
      have hyL : L y := path_target path
      have hp : Parents C D x y := ⟨lc hyL, edge⟩
      have hf : F X x := by
        apply Or.inr
        refine ⟨lc hxL, ⟨y, hp⟩, ?_⟩
        simp only [StatusMechanism, hxL, ↓reduceIte, OrGate]
        exact Or.inr ⟨y, hp, ih, hp⟩
      rw [fixedF] at hf
      exact hf
  have zpath : ∀ x, InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) x → ¬ X x := by
    intro x h
    obtain ⟨b, ⟨hbRoot, hbNotU⟩, path⟩ := h
    induction path with
    | refl _ =>
      intro hbX
      have hf : F X b := by rw [fixedF]; exact hbX
      rcases hf with hu | ⟨_, ⟨p, hp⟩, _⟩
      · exact hbNotU hu
      · exact hbRoot.2 p hp
    | @step y x path hxZ edge ih =>
      intro hxX
      have hxL : ¬ L x := by intro hl; exact (part.2.1 x) ⟨hl, hxZ⟩
      have hxNotU : ¬ U x := by intro hu; exact hxL (cond.1 hu)
      have hyZ : Z y := path_target path
      have hp : Parents C D x y := ⟨zc hyZ, edge⟩
      have hf : F X x := by rw [fixedF]; exact hxX
      rcases hf with hu | ⟨_, _, hGate⟩
      · exact hxNotU hu
      · simp only [StatusMechanism, hxL, hxZ, ↓reduceIte, AndGate] at hGate
        exact ih (hGate y hp).1
  constructor
  · intro x hx
    apply lpath x
    rw [cond.2.2.1]
    exact hx
  · intro x hx
    refine ⟨xc hx, ?_⟩
    intro hz
    apply zpath x ?_ hx
    rw [cond.2.2.2.1]
    exact hz

/-- Under the partition, pattern and legal-context conditions, if this exact
witness is admissible then its least and greatest fixed points are prescribed. -/
theorem witness_extrema_of_admissible {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D))
    (adm : Mechanism C D (StatusMechanism C D L Z Q)) :
    Least (Step C D (StatusMechanism C D L Z Q) U) = L ∧
      Greatest (Step C D (StatusMechanism C D L Z Q) U) = (fun x => C x ∧ ¬ Z x) := by
  let f := StatusMechanism C D L Z Q
  have fixes := status_two_fixed_points part cond
  have lowFix := least_fixed (step_monotone adm U)
  have highFix := greatest_fixed (step_monotone adm U)
  have lowForces := status_forces_paths part cond ctx lowFix
  have highForces := status_forces_paths part cond ctx highFix
  refine ⟨?_, ?_⟩
  · apply funext
    intro x
    apply propext
    constructor
    · intro hx; exact (fixed_bounds fixes.1).1 hx
    · intro hx; exact lowForces.1 hx
  · apply funext
    intro x
    apply propext
    constructor
    · intro hx; exact highForces.2 hx
    · intro hx; exact (fixed_bounds fixes.2).2 hx

end DeterminationPatterns
