module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for relevant endpoint attainment. -/
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

end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- Source region criterion: carrier and root containment, internal root reach,
and closure under the universal-parent operator. -/
def RegionConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (K : Region α) : Prop :=
  Sub K C ∧ Sub (Roots C D) K ∧ InternalReach K D (Roots C D) = K ∧
  (∀ x, C x → (∀ y, Parents C D x y → K y) → K x)

theorem path_source {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (h : InternalPath A D b x) : A b := by
  induction h with
  | refl hx => exact hx
  | step _ _ _ ih => exact ih

theorem reach_step {α : Type u} {K U : Region α} {D : α → α → Prop}
    {y x : α} (hy : InternalReach K D U y) (hx : K x) (edge : D y x) :
    InternalReach K D U x := by
  obtain ⟨b, hb, hp⟩ := hy
  exact ⟨b, hb, InternalPath.step hp hx edge⟩

theorem path_in_reached {α : Type u} {K U : Region α} {D : α → α → Prop}
    {b x : α} (p : InternalPath K D b x) (hb : U b) :
    InternalPath (InternalReach K D U) D b x := by
  induction p with
  | refl hk => exact InternalPath.refl _ ⟨_, hb, InternalPath.refl _ hk⟩
  | step path hx edge ih =>
    exact InternalPath.step ih ⟨_, hb, InternalPath.step path hx edge⟩ edge

theorem path_outside_reached {α : Type u} {K U : Region α} {D : α → α → Prop}
    {b x : α} (p : InternalPath K D b x) :
    ¬ InternalReach K D U x →
      InternalPath (fun z => K z ∧ ¬ InternalReach K D U z) D b x := by
  induction p with
  | refl hk =>
    intro hn
    exact InternalPath.refl _ ⟨hk, hn⟩
  | @step y x path hx edge ih =>
    intro hn
    have hy : ¬ InternalReach K D U y := by
      intro hr
      exact hn (reach_step hr hx edge)
    exact InternalPath.step (ih hy) ⟨hx, hn⟩ edge

/-- Every region satisfying the exact criterion is realized at a legal root context by an admissible, fully edge-relevant mechanism. -/
theorem region_conditions_sufficient {α : Type u} {C K U : Region α}
    {D : α → α → Prop} (reg : RegionConditions C D K)
    (ctx : Sub U (Roots C D)) :
    ∃ f, Mechanism C D f ∧ Relevant C D f ∧ Determined C (Step C D f U) = K := by
  classical
  let L := InternalReach K D U
  let Z : Region α := fun x => K x ∧ ¬ L x
  let Q : Region α := fun x => C x ∧ ¬ K x
  have lk : Sub L K := by intro x ⟨_, _, hp⟩; exact path_target hp
  have uk : Sub U K := by intro x hu; exact reg.2.1 (ctx hu)
  have ul : Sub U L := by
    intro x hu
    exact ⟨x, hu, InternalPath.refl x (uk hu)⟩
  have part : StatusPartition C L Z Q := by
    constructor
    · intro x
      constructor
      · intro hc
        by_cases hk : K x
        · by_cases hl : L x
          · exact Or.inl hl
          · exact Or.inr (Or.inl ⟨hk, hl⟩)
        · exact Or.inr (Or.inr ⟨hc, hk⟩)
      · intro h
        rcases h with hl | ⟨hk, _⟩ | ⟨hc, _⟩
        · exact reg.1 (lk hl)
        · exact reg.1 hk
        · exact hc
    · constructor
      · intro x ⟨hl, _, hnot⟩; exact hnot hl
      · constructor
        · intro x ⟨hl, _, hnot⟩; exact hnot (lk hl)
        · intro x ⟨⟨hk, _⟩, _, hnot⟩; exact hnot hk
  have rootZ : Sub (fun x => Roots C D x ∧ ¬ U x) Z := by
    intro x ⟨hr, hn⟩
    refine ⟨reg.2.1 hr, ?_⟩
    intro hL
    rcases path_last_or_seed hL with hu | ⟨y, hyK, edge⟩
    · exact hn hu
    · exact hr.2 y ⟨reg.1 hyK, edge⟩
  have reachL : InternalReach L D U = L := by
    apply funext
    intro x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro h
      obtain ⟨b, hb, hp⟩ := h
      exact ⟨b, hb, path_in_reached hp hb⟩
  have reachZ : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    apply funext
    intro x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨hk, hnL⟩
      have hr : InternalReach K D (Roots C D) x := by rw [reg.2.2.1]; exact hk
      obtain ⟨b, hbRoot, hp⟩ := hr
      have zp : InternalPath Z D b x := path_outside_reached hp hnL
      have hbNotL : ¬ L b := (path_source zp).2
      have hbNotU : ¬ U b := fun hu => hbNotL (ul hu)
      exact ⟨b, ⟨hbRoot, hbNotU⟩, zp⟩
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y := by
    intro x ⟨hc, hnK⟩
    apply Classical.byContradiction
    intro hn
    apply hnK
    apply reg.2.2.2 x hc
    intro y hp
    apply Classical.byContradiction
    intro hyNotK
    exact hn ⟨y, hp, hp.1, hyNotK⟩
  have cond : PatternConditions C D U L Z Q := ⟨ul, rootZ, reachL, reachZ, qp⟩
  have witness := pattern_witness_extrema part cond ctx
  refine ⟨StatusMechanism C D L Z Q, witness.1, witness.2.1, ?_⟩
  funext x
  apply propext
  unfold Determined
  rw [witness.2.2.1, witness.2.2.2]
  constructor
  · intro h
    rcases h with hl | ⟨hc, hn⟩
    · exact lk hl
    · apply Classical.byContradiction
      intro hnK
      exact hn ⟨hc, fun hz => hnK hz.1⟩
  · intro hk
    by_cases hl : L x
    · exact Or.inl hl
    · exact Or.inr ⟨reg.1 hk, fun h => h.2 ⟨hk, hl⟩⟩


end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- Dependency edges whose endpoints both lie in `A`. -/
def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x

/-- Finite reachability from carrier roots. -/
def RootReachable {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  InternalReach C D (Roots C D)

/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x

/-- The root-reachable region satisfies the exact attainable-region criterion. -/
theorem root_reachable_conditions {α : Type u} (C : Region α) (D : α → α → Prop) :
    RegionConditions C D (RootReachable C D) := by
  classical
  let R := RootReachable C D
  have rc : Sub R C := by intro x ⟨_, _, hp⟩; exact path_target hp
  have roots : Sub (Roots C D) R := by
    intro x hx
    exact ⟨x, hx, InternalPath.refl x hx.1⟩
  have reach : InternalReach R D (Roots C D) = R := by
    funext x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨b, hb, hp⟩
      exact ⟨b, hb, path_in_reached hp hb⟩
  have closed : ∀ x, C x → (∀ y, Parents C D x y → R y) → R x := by
    intro x hx allp
    by_cases hp : ∃ y, Parents C D x y
    · obtain ⟨y, hy⟩ := hp
      exact reach_step (allp y hy) hx hy.2
    · exact roots ⟨hx, fun y hy => hp ⟨y, hy⟩⟩
  exact ⟨rc, roots, reach, closed⟩

/-- The accessible region satisfies the exact attainable-region criterion. -/
theorem accessible_region_conditions {α : Type u} (C : Region α) (D : α → α → Prop) :
    RegionConditions C D (AccessibleRegion C D) := by
  classical
  let W := AccessibleRegion C D
  have wc : Sub W C := by intro x hx; exact hx.1
  have roots : Sub (Roots C D) W := by
    intro x ⟨hc, hno⟩
    refine ⟨hc, Acc.intro x ?_⟩
    intro y ⟨hyC, _, hyD⟩
    exact False.elim (hno y ⟨hyC, hyD⟩)
  have reachable : ∀ x, Acc (RestrictedEdge C D) x → C x → InternalReach W D (Roots C D) x := by
    intro x ha
    induction ha with
    | intro x hacc ih =>
      intro hc
      have wx : W x := ⟨hc, Acc.intro x hacc⟩
      by_cases hp : ∃ y, Parents C D x y
      · obtain ⟨y, hy⟩ := hp
        have edge : RestrictedEdge C D y x := ⟨hy.1, hc, hy.2⟩
        exact reach_step (ih y edge hy.1) wx hy.2
      · have root : Roots C D x := ⟨hc, fun y hy => hp ⟨y, hy⟩⟩
        exact ⟨x, root, InternalPath.refl x wx⟩
  have reach : InternalReach W D (Roots C D) = W := by
    funext x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨hc, ha⟩; exact reachable x ha hc
  have closed : ∀ x, C x → (∀ y, Parents C D x y → W y) → W x := by
    intro x hc allp
    refine ⟨hc, Acc.intro x ?_⟩
    intro y ⟨hyC, _, hyD⟩
    exact (allp y ⟨hyC, hyD⟩).2
  exact ⟨wc, roots, reach, closed⟩

/-- At a fixed legal context, both endpoints of the determination interval
are attained by fully edge-relevant admissible mechanisms. The witnesses may differ. -/
theorem relevant_endpoint_attainment {α : Type u} {C U : Region α}
    {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    ∃ f g, Mechanism C D f ∧ Relevant C D f ∧
      Determined C (Step C D f U) = AccessibleRegion C D ∧
      Mechanism C D g ∧ Relevant C D g ∧
      Determined C (Step C D g U) = RootReachable C D := by
  obtain ⟨f, admF, relF, eqF⟩ := region_conditions_sufficient (accessible_region_conditions C D) ctx
  obtain ⟨g, admG, relG, eqG⟩ := region_conditions_sufficient (root_reachable_conditions C D) ctx
  exact ⟨f, g, admF, relF, eqF, admG, relG, eqG⟩

end DeterminationPatterns
