module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the exact pattern realization results. -/
namespace DeterminationPatterns
universe u
/-! ## Carrier, mechanism, context and fixed points -/

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

/-! ## Paths inside a designated region -/

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


end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-! ## Pattern criteria and explicit witness -/

/-- The carrier is exactly the disjoint union of the three statuses. -/
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

/-- The source's explicit OR/AND/split witness. -/
noncomputable def StatusMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (L Z Q : Region α) (x : α) (S : Region α) : Prop := by
  classical
  exact if L x then OrGate (Parents C D x) S
    else if Z x then AndGate (Parents C D x) S
    else SplitGate (Parents C D x) L Z Q S

theorem status_mechanism_admissible {α : Type u} {C L Z Q : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y) :
    Mechanism C D (StatusMechanism C D L Z Q) := by
  classical
  intro x hx
  by_cases hl : L x
  · simp only [StatusMechanism, hl, ↓reduceIte]
    constructor
    · intro A B hAB h
      rcases h with hnone | ⟨y, hp, hy⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨y, hp, hAB hy⟩
    constructor
    · simp [OrGate]
    · by_cases hp : ∃ y, Parents C D x y
      · obtain ⟨y, hy⟩ := hp
        exact Or.inr ⟨y, hy, hy⟩
      · exact Or.inl (fun y hy => hp ⟨y, hy⟩)
  · by_cases hz : Z x
    · simp only [StatusMechanism, hl, hz, ↓reduceIte]
      constructor
      · intro A B hAB h y hy
        exact hAB (h y hy)
      constructor
      · simp [AndGate]
      · intro y hy; exact hy
    · have hq : Q x := by
        rcases (part.1 x).mp hx with h | h | h
        · exact False.elim (hl h)
        · exact False.elim (hz h)
        · exact h
      obtain ⟨q, hqp, hqq⟩ := qp x hq
      simp only [StatusMechanism, hl, hz, ↓reduceIte]
      constructor
      · intro A B hAB h
        rcases h with ⟨⟨y, hp, hq, hy⟩, ha⟩ | ⟨y, hp, hz, hy⟩
        · exact Or.inl ⟨⟨y, hp, hq, hAB hy⟩, fun z hz => hAB (ha z hz)⟩
        · exact Or.inr ⟨y, hp, hz, hAB hy⟩
      constructor
      · constructor
        · intro h
          rcases h with ⟨⟨_, _, _, bad⟩, _⟩ | ⟨_, _, _, bad⟩ <;> exact False.elim bad
        · intro hnone
          exact False.elim (hnone q hqp)
      · exact Or.inl ⟨⟨q, hqp, hqq, hqp⟩, fun _ h => h.1⟩

theorem status_mechanism_relevant {α : Type u} {C L Z Q : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y) :
    Relevant C D (StatusMechanism C D L Z Q) := by
  classical
  intro x hx y hy
  by_cases hl : L x
  · refine ⟨(fun _ => False), ?_, ?_, ?_⟩
    · intro z hz; exact False.elim hz
    · simp only [StatusMechanism, hl, ↓reduceIte, OrGate]
      intro h
      rcases h with hnone | ⟨_, _, bad⟩
      · exact hnone y hy
      · exact False.elim bad
    · simp only [StatusMechanism, hl, ↓reduceIte, OrGate]
      exact Or.inr ⟨y, hy, Or.inl rfl⟩
  · by_cases hz : Z x
    · refine ⟨(fun z => Parents C D x z ∧ z ≠ y), ?_, ?_, ?_⟩
      · intro z h; exact h
      · simp only [StatusMechanism, hl, hz, ↓reduceIte, AndGate]
        intro h
        exact (h y hy).2 rfl
      · simp only [StatusMechanism, hl, hz, ↓reduceIte, AndGate]
        intro z hp
        by_cases heq : z = y
        · exact Or.inl heq
        · exact Or.inr ⟨hp, heq⟩
    · have hq : Q x := by
        rcases (part.1 x).mp hx with h | h | h
        · exact False.elim (hl h)
        · exact False.elim (hz h)
        · exact h
      have yCases := (part.1 y).mp hy.1
      rcases yCases with hyL | hyZ | hyQ
      · obtain ⟨q, hqP, hqQ⟩ := qp x hq
        have hqne : q ≠ y := by
          intro eq
          subst q
          exact (part.2.2.1 y) ⟨hyL, hqQ⟩
        let S : Region α := fun z => z = q ∨ (Parents C D x z ∧ L z ∧ z ≠ y)
        refine ⟨S, ?_, ?_, ?_⟩
        · intro z h
          rcases h with eq | ⟨hp, _, hne⟩
          · subst z; exact ⟨hqP, hqne⟩
          · exact ⟨hp, hne⟩
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          intro h
          rcases h with ⟨_, hall⟩ | ⟨z, hp, hz', hS⟩
          · have hSy := hall y ⟨hy, hyL⟩
            rcases hSy with heq | ⟨_, _, hne⟩
            · exact hqne heq.symm
            · exact hne rfl
          · rcases hS with heq | ⟨_, hL, _⟩
            · subst z; exact (part.2.2.2 q) ⟨hz', hqQ⟩
            · exact (part.2.1 z) ⟨hL, hz'⟩
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          apply Or.inl
          constructor
          · exact ⟨q, hqP, hqQ, Or.inr (Or.inl rfl)⟩
          · intro z ⟨hp, hL⟩
            by_cases heq : z = y
            · exact Or.inl heq
            · exact Or.inr (Or.inr ⟨hp, hL, heq⟩)
      · refine ⟨(fun _ => False), ?_, ?_, ?_⟩
        · intro z h; exact False.elim h
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          intro h
          rcases h with ⟨⟨_, _, _, bad⟩, _⟩ | ⟨_, _, _, bad⟩ <;> exact False.elim bad
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          exact Or.inr ⟨y, hy, hyZ, Or.inl rfl⟩
      · let S : Region α := fun z => Parents C D x z ∧ L z
        refine ⟨S, ?_, ?_, ?_⟩
        · intro z ⟨hp, hL⟩
          constructor
          · exact hp
          · intro heq
            subst z
            exact (part.2.2.1 y) ⟨hL, hyQ⟩
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          intro h
          rcases h with ⟨⟨z, _, hQ, ⟨_, hL⟩⟩, _⟩ | ⟨z, _, hZ, ⟨_, hL⟩⟩
          · exact (part.2.2.1 z) ⟨hL, hQ⟩
          · exact (part.2.1 z) ⟨hL, hZ⟩
        · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
          exact Or.inl ⟨⟨y, hy, hyQ, Or.inl rfl⟩, fun _ h => Or.inr h⟩

/-! ## Sufficiency: fixed points and extrema -/

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

/-- The stated OR/AND/split witness is admissible and edge-relevant, with
least fixed point `L` and greatest fixed point the carrier outside `Z`. -/
theorem pattern_witness_extrema {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D)) :
    let f := StatusMechanism C D L Z Q
    Mechanism C D f ∧ Relevant C D f ∧ Least (Step C D f U) = L ∧
      Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x) := by
  let f := StatusMechanism C D L Z Q
  have adm : Mechanism C D f := status_mechanism_admissible part cond.2.2.2.2
  have rel : Relevant C D f := status_mechanism_relevant part cond.2.2.2.2
  have fixes := status_two_fixed_points part cond
  have lowFix := least_fixed (step_monotone adm U)
  have highFix := greatest_fixed (step_monotone adm U)
  have lowForces := status_forces_paths part cond ctx lowFix
  have highForces := status_forces_paths part cond ctx highFix
  refine ⟨adm, rel, ?_, ?_⟩
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

namespace DeterminationPatterns
universe u

/-! ## Necessity: every realizing mechanism -/

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

theorem contextual_greatest_internal_zero_paths {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    InternalReach (fun x => C x ∧ ¬ Greatest (Step C D f U) x) D
      (fun x => Roots C D x ∧ ¬ U x) =
      (fun x => C x ∧ ¬ Greatest (Step C D f U) x) := by
  classical
  let F := Step C D f U
  let G := Greatest F
  let Z : Region α := fun x => C x ∧ ¬ G x
  let R := InternalReach Z D (fun x => Roots C D x ∧ ¬ U x)
  let Y : Region α := fun x => C x ∧ ¬ R x
  have hm : Monotone F := step_monotone adm U
  have gf : Fixed F G := greatest_fixed hm
  have gc : Sub G C := contextual_fixed_carrier ctx gf
  have rz : Sub R Z := by intro x h; obtain ⟨_, _, hp⟩ := h; exact path_target hp
  have gy : Sub G Y := by
    intro x hx
    refine ⟨gc hx, ?_⟩
    intro hr
    exact (rz hr).2 hx
  have post : Sub Y (F Y) := by
    intro x ⟨hxC, hxNotR⟩
    by_cases hxG : G x
    · have hFG : F G x := by rw [gf]; exact hxG
      exact hm G Y gy hFG
    · have hxZ : Z x := ⟨hxC, hxG⟩
      have hxNotU : ¬ U x := by
        intro hu
        have hFG : F G x := Or.inl hu
        rw [gf] at hFG
        exact hxG hFG
      have hparent : ∃ y, Parents C D x y := by
        apply Classical.byContradiction
        intro hnone
        have root : Roots C D x := ⟨hxC, fun y hy => hnone ⟨y, hy⟩⟩
        have rx : R x := ⟨x, ⟨root, hxNotU⟩, InternalPath.refl x hxZ⟩
        exact hxNotR rx
      have noR : ∀ y, Parents C D x y → ¬ R y := by
        intro y hyP hyR
        obtain ⟨b, hb, path⟩ := hyR
        have rx : R x := ⟨b, hb, InternalPath.step path hxZ hyP.2⟩
        exact hxNotR rx
      have inputs : (fun y => Y y ∧ Parents C D x y) = Parents C D x := by
        funext y
        apply propext
        constructor
        · intro h; exact h.2
        · intro hp; exact ⟨⟨hp.1, noR y hp⟩, hp⟩
      apply Or.inr
      refine ⟨hxC, hparent, ?_⟩
      rw [inputs]
      exact (adm x hxC).2.2
  have yz : Sub Y G := le_greatest F Y post
  apply funext
  intro x
  apply propext
  constructor
  · intro hr; exact rz hr
  · intro hx
    apply Classical.byContradiction
    intro hn
    exact hx.2 (yz ⟨hx.1, hn⟩)

theorem ambiguity_has_ambiguous_parent {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (_ctx : Sub U (Roots C D)) {x : α}
    (hxG : Greatest (Step C D f U) x) (hxNotL : ¬ Least (Step C D f U) x) :
    ∃ y, Parents C D x y ∧ Greatest (Step C D f U) y ∧
      ¬ Least (Step C D f U) y := by
  classical
  let F := Step C D f U
  let L := Least F
  let G := Greatest F
  have hm : Monotone F := step_monotone adm U
  have lf : Fixed F L := least_fixed hm
  have gf : Fixed F G := greatest_fixed hm
  have lg : Sub L G := (fixed_bounds gf).1
  apply Classical.byContradiction
  intro hn
  have eq : (fun y => L y ∧ Parents C D x y) = (fun y => G y ∧ Parents C D x y) := by
    funext y
    apply propext
    constructor
    · intro h; exact ⟨lg h.1, h.2⟩
    · intro h
      have hyL : L y := by
        apply Classical.byContradiction
        intro hnot
        exact hn ⟨y, h.2, h.1, hnot⟩
      exact ⟨hyL, h.2⟩
  have hfg : F G x := by rw [gf]; exact hxG
  have hfl : F L x := by
    rcases hfg with hu | ⟨hc, hp, hf⟩
    · exact Or.inl hu
    · apply Or.inr
      refine ⟨hc, hp, ?_⟩
      rw [eq]
      exact hf
  rw [lf] at hfl
  exact hxNotL hfl

/-- Any admissible mechanism realizing these extremal regions satisfies the
pattern conditions; edge relevance is not needed for this direction. -/
theorem realized_pattern_necessary {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (part : StatusPartition C L Z Q) (ctx : Sub U (Roots C D))
    (adm : Mechanism C D f) (low : Least (Step C D f U) = L)
    (high : Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) :
    PatternConditions C D U L Z Q := by
  classical
  let F := Step C D f U
  have lf : Fixed F L := by
    have h := least_fixed (step_monotone adm U)
    rw [low] at h
    exact h
  have gf : Fixed F (fun x => C x ∧ ¬ Z x) := by
    have h := greatest_fixed (step_monotone adm U)
    rw [high] at h
    exact h
  have zc : Sub Z C := by intro x hz; exact (part.1 x).mpr (Or.inr (Or.inl hz))
  have qc : Sub Q C := by intro x hq; exact (part.1 x).mpr (Or.inr (Or.inr hq))
  have ul : Sub U L := by
    intro x hu
    have h : F L x := Or.inl hu
    rw [lf] at h
    exact h
  have rootZ : Sub (fun x => Roots C D x ∧ ¬ U x) Z := by
    intro x ⟨hroot, hnot⟩
    have iff := contextual_fixed_roots ctx gf x hroot
    apply Classical.byContradiction
    intro hnz
    exact hnot (iff.mp ⟨hroot.1, hnz⟩)
  have lpath : InternalReach L D U = L := by
    have h := contextual_least_internal_paths adm ctx
    rw [low] at h
    exact h
  have zpath : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    have h := contextual_greatest_internal_zero_paths adm ctx
    rw [high] at h
    have zform : (fun x => C x ∧ ¬ (C x ∧ ¬ Z x)) = Z := by
      funext x
      apply propext
      constructor
      · intro ⟨hc, hn⟩
        apply Classical.byContradiction
        intro hnz
        exact hn ⟨hc, hnz⟩
      · intro hz
        exact ⟨zc hz, fun h => h.2 hz⟩
    rw [zform] at h
    exact h
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y := by
    intro x hxQ
    have hxNotL : ¬ L x := by intro hl; exact (part.2.2.1 x) ⟨hl, hxQ⟩
    have hxNotZ : ¬ Z x := by intro hz; exact (part.2.2.2 x) ⟨hz, hxQ⟩
    have hxG : Greatest F x := by rw [high]; exact ⟨qc hxQ, hxNotZ⟩
    have hxNotLeast : ¬ Least F x := by rw [low]; exact hxNotL
    obtain ⟨y, hyP, hyG, hyNotLeast⟩ := ambiguity_has_ambiguous_parent adm ctx hxG hxNotLeast
    have hyNotL : ¬ L y := by rw [← low]; exact hyNotLeast
    have hyNotZ : ¬ Z y := by rw [high] at hyG; exact hyG.2
    have hyQ : Q y := by
      rcases (part.1 y).mp hyP.1 with hyL | hyZ | hyQ
      · exact False.elim (hyNotL hyL)
      · exact False.elim (hyNotZ hyZ)
      · exact hyQ
    exact ⟨y, hyP, hyQ⟩
  exact ⟨ul, rootZ, lpath, zpath, qp⟩

/-! ## Exact pattern realization -/

/-- A disjoint forced-on, forced-off, and ambiguous partition is realized by
one admissible edge-relevant mechanism exactly when the pattern conditions hold. -/
theorem exact_pattern_from_components {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Least (Step C D f U) = L ∧
      Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) ↔
      PatternConditions C D U L Z Q := by
  constructor
  · rintro ⟨f, adm, _, low, high⟩
    exact realized_pattern_necessary part ctx adm low high
  · intro cond
    exact ⟨StatusMechanism C D L Z Q, pattern_witness_extrema part cond ctx⟩

end DeterminationPatterns
