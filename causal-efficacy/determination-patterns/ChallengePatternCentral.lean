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
  have rl : Sub R L := fun {x} ⟨_, _, hp⟩ => path_target hp
  have pre : Sub (F R) R :=
    fun {x} hx =>
      let hxl : L x := Eq.mp (congrFun lf x) (lm R L rl hx)
      hx.elim
        (fun hu => ⟨x, hu, InternalPath.refl x hxl⟩)
        (fun ⟨hc, ⟨p, hp⟩, hf⟩ =>
          let parent : ∃ y, R y ∧ Parents C D x y :=
            Classical.byContradiction (fun hn =>
              let eq : (fun y => R y ∧ Parents C D x y) = (fun _ => False) :=
                funext (fun y => propext ⟨fun hy => hn ⟨y, hy⟩, fun hy => False.elim hy⟩)
              let hf0 : f x (fun _ => False) := Eq.mp (congrArg (f x) eq) hf
              (adm x hc).2.1.mp hf0 p hp)
          match parent with
          | ⟨y, ⟨b, hb, path⟩, hyP⟩ => ⟨b, hb, InternalPath.step path hxl hyP.2⟩)
  exact funext (fun _x => propext ⟨fun hx => rl hx, fun hx => least_le F R pre hx⟩)


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
    refine ⟨?_, ?_, ?_⟩
    · exact fun A B hAB h => h.elim
        (fun hnone => Or.inl hnone)
        (fun ⟨y, hp, hy⟩ => Or.inr ⟨y, hp, hAB hy⟩)
    · simp [OrGate]
    · by_cases hp : ∃ y, Parents C D x y
      · obtain ⟨y, hy⟩ := hp
        exact Or.inr ⟨y, hy, hy⟩
      · exact Or.inl (fun y hy => hp ⟨y, hy⟩)
  · by_cases hz : Z x
    · simp only [StatusMechanism, hl, hz, ↓reduceIte]
      refine ⟨(fun A B hAB h y hy => hAB (h y hy)), ?_, fun y hy => hy⟩
      simp [AndGate]
    · have hq : Q x :=
        ((part.1 x).mp hx).elim (fun h => False.elim (hl h))
          (fun h => h.elim (fun h => False.elim (hz h)) id)
      obtain ⟨q, hqp, hqq⟩ := qp x hq
      simp only [StatusMechanism, hl, hz, ↓reduceIte]
      refine ⟨?_, ?_, Or.inl ⟨⟨q, hqp, hqq, hqp⟩, fun _ h => h.1⟩⟩
      · exact fun A B hAB h => h.elim
          (fun ⟨⟨y, hp, hq, hy⟩, ha⟩ =>
            Or.inl ⟨⟨y, hp, hq, hAB hy⟩, fun z hz => hAB (ha z hz)⟩)
          (fun ⟨y, hp, hz, hy⟩ => Or.inr ⟨y, hp, hz, hAB hy⟩)
      · exact ⟨fun h => h.elim
          (fun ⟨⟨_, _, _, bad⟩, _⟩ => False.elim bad)
          (fun ⟨_, _, _, bad⟩ => False.elim bad),
        fun hnone => False.elim (hnone q hqp)⟩

/-- An edge into a forced-on vertex is relevant for the OR gate. -/
theorem status_relevant_L {α : Type u} {C L Z Q : Region α} {D : α → α → Prop} {x y : α}
    (hl : L x) (hy : Parents C D x y) :
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ StatusMechanism C D L Z Q x S ∧
        StatusMechanism C D L Z Q x (fun z => z = y ∨ S z) := by
  classical
  refine ⟨(fun _ => False), ?_, ?_, ?_⟩
  · intro z hz; exact False.elim hz
  · simp only [StatusMechanism, hl, ↓reduceIte, OrGate]
    intro h
    rcases h with hnone | ⟨_, _, bad⟩
    · exact hnone y hy
    · exact False.elim bad
  · simp only [StatusMechanism, hl, ↓reduceIte, OrGate]
    exact Or.inr ⟨y, hy, Or.inl rfl⟩

/-- An edge into a forced-off vertex is relevant for the AND gate. -/
theorem status_relevant_Z {α : Type u} {C L Z Q : Region α} {D : α → α → Prop} {x y : α}
    (hl : ¬ L x) (hz : Z x) (hy : Parents C D x y) :
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ StatusMechanism C D L Z Q x S ∧
        StatusMechanism C D L Z Q x (fun z => z = y ∨ S z) := by
  classical
  refine ⟨(fun z => Parents C D x z ∧ z ≠ y), ?_, ?_, ?_⟩
  · intro z h; exact h
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, AndGate]
    intro h
    exact (h y hy).2 rfl
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, AndGate]
    intro z hp
    by_cases heq : z = y
    · exact Or.inl heq
    · exact Or.inr ⟨hp, heq⟩

/-- A forced-on parent is relevant for the ambiguous split gate. -/
theorem status_relevant_Q_L {α : Type u} {C L Z Q : Region α} {D : α → α → Prop} {x y : α}
    (part : StatusPartition C L Z Q) (hl : ¬ L x) (hz : ¬ Z x)
    (hy : Parents C D x y) (hyL : L y) {q : α}
    (hqP : Parents C D x q) (hqQ : Q q) :
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ StatusMechanism C D L Z Q x S ∧
        StatusMechanism C D L Z Q x (fun z => z = y ∨ S z) := by
  classical
  have hqne : q ≠ y :=
    fun eq => (part.2.2.1 y) ⟨hyL, Eq.mp (congrArg Q eq) hqQ⟩
  let S : Region α := fun z => z = q ∨ (Parents C D x z ∧ L z ∧ z ≠ y)
  refine ⟨S, ?_, ?_, ?_⟩
  · exact fun {z} h => h.elim
      (fun eq => Eq.mpr (congrArg (fun t => Parents C D x t ∧ t ≠ y) eq) ⟨hqP, hqne⟩)
      (fun ⟨hp, _, hne⟩ => ⟨hp, hne⟩)
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
    exact fun h => h.elim
      (fun ⟨_, hall⟩ => (hall y ⟨hy, hyL⟩).elim
        (fun eq => hqne eq.symm) (fun ⟨_, _, hne⟩ => hne rfl))
      (fun ⟨z, _, hz', hS⟩ => hS.elim
        (fun eq => (part.2.2.2 z) ⟨hz', Eq.mpr (congrArg Q eq) hqQ⟩)
        (fun ⟨_, hL, _⟩ => (part.2.1 z) ⟨hL, hz'⟩))
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
    exact Or.inl ⟨⟨q, hqP, hqQ, Or.inr (Or.inl rfl)⟩,
      fun z ⟨hp, hL⟩ => if eq : z = y then Or.inl eq
        else Or.inr (Or.inr ⟨hp, hL, eq⟩)⟩

/-- A forced-off parent is relevant for the ambiguous split gate. -/
theorem status_relevant_Q_Z {α : Type u} {C L Z Q : Region α} {D : α → α → Prop} {x y : α}
    (hl : ¬ L x) (hz : ¬ Z x) (hy : Parents C D x y) (hyZ : Z y) :
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ StatusMechanism C D L Z Q x S ∧
        StatusMechanism C D L Z Q x (fun z => z = y ∨ S z) := by
  classical
  refine ⟨(fun _ => False), ?_, ?_, ?_⟩
  · intro z h; exact False.elim h
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
    intro h
    rcases h with ⟨⟨_, _, _, bad⟩, _⟩ | ⟨_, _, _, bad⟩ <;> exact False.elim bad
  · simp only [StatusMechanism, hl, hz, ↓reduceIte, SplitGate]
    exact Or.inr ⟨y, hy, hyZ, Or.inl rfl⟩

/-- An ambiguous parent is relevant for the ambiguous split gate. -/
theorem status_relevant_Q_Q {α : Type u} {C L Z Q : Region α} {D : α → α → Prop} {x y : α}
    (part : StatusPartition C L Z Q) (hl : ¬ L x) (hz : ¬ Z x)
    (hy : Parents C D x y) (hyQ : Q y) :
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ StatusMechanism C D L Z Q x S ∧
        StatusMechanism C D L Z Q x (fun z => z = y ∨ S z) := by
  classical
  let S : Region α := fun z => Parents C D x z ∧ L z
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


theorem status_mechanism_relevant {α : Type u} {C L Z Q : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y) :
    Relevant C D (StatusMechanism C D L Z Q) := by
  classical
  intro x hx y hy
  by_cases hl : L x
  · exact status_relevant_L hl hy
  · by_cases hz : Z x
    · exact status_relevant_Z hl hz hy
    · have hq : Q x := by
        rcases (part.1 x).mp hx with h | h | h
        · exact False.elim (hl h)
        · exact False.elim (hz h)
        · exact h
      rcases (part.1 y).mp hy.1 with hyL | hyZ | hyQ
      · obtain ⟨q, hqP, hqQ⟩ := qp x hq
        exact status_relevant_Q_L part hl hz hy hyL hqP hqQ
      · exact status_relevant_Q_Z hl hz hy hyZ
      · exact status_relevant_Q_Q part hl hz hy hyQ

/-! ## Sufficiency: fixed points and extrema -/

theorem path_last_or_seed {α : Type u} {A B : Region α} {D : α → α → Prop}
    {x : α} (h : InternalReach A D B x) :
    B x ∨ ∃ y, A y ∧ D y x := by
  obtain ⟨b, hb, hp⟩ := h
  cases hp with
  | refl _ => exact Or.inl hb
  | step path _ edge => exact Or.inr ⟨_, path_target path, edge⟩

/-- The update sends the proposed forced-on region into itself. -/
theorem status_low_forward {α : Type u} {C L Z Q U : Region α} {D : α → α → Prop}
    (part : StatusPartition C L Z Q) (ul : Sub U L) (zp : ∀ x, Z x → (∀ y, ¬ Parents C D x y) ∨ ∃ y, Parents C D x y ∧ Z y) :
    Sub (Step C D (StatusMechanism C D L Z Q) U L) L := by
  classical
  intro x h
  rcases h with hu | ⟨hxC, ⟨p, hp⟩, hf⟩
  · exact ul hu
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

/-- Every proposed forced-on vertex is in its update. -/
theorem status_low_backward {α : Type u} {C L Z Q U : Region α} {D : α → α → Prop}
    (lc : Sub L C) (lu : ∀ x, L x → U x ∨ ∃ y, Parents C D x y ∧ L y) :
    Sub L (Step C D (StatusMechanism C D L Z Q) U L) := by
  classical
  intro x hxL
  rcases lu x hxL with hu | ⟨y, hyP, hyL⟩
  · exact Or.inl hu
  · apply Or.inr
    refine ⟨lc hxL, ⟨y, hyP⟩, ?_⟩
    simp only [StatusMechanism, hxL, ↓reduceIte, OrGate]
    exact Or.inr ⟨y, hyP, hyL, hyP⟩

/-- The update preserves the carrier outside the forced-off region. -/
theorem status_high_forward {α : Type u} {C L Z Q U : Region α} {D : α → α → Prop}
    (part : StatusPartition C L Z Q) (ul : Sub U L)
    (lc : Sub L C) (unotz : ∀ x, U x → ¬ Z x) (zp : ∀ x, Z x → (∀ y, ¬ Parents C D x y) ∨ ∃ y, Parents C D x y ∧ Z y) :
    Sub (Step C D (StatusMechanism C D L Z Q) U (fun x => C x ∧ ¬ Z x)) (fun x => C x ∧ ¬ Z x) := by
  classical
  intro x h
  rcases h with hu | ⟨hxC, ⟨p, hp⟩, hf⟩
  · exact ⟨lc (ul hu), unotz x hu⟩
  · refine ⟨hxC, ?_⟩
    intro hxZ
    have hxL : ¬ L x := by intro hl; exact (part.2.1 x) ⟨hl, hxZ⟩
    simp only [StatusMechanism, hxL, hxZ, ↓reduceIte, AndGate] at hf
    rcases zp x hxZ with hroot | ⟨y, hyP, hyZ⟩
    · exact hroot p hp
    · exact (hf y hyP).1.2 hyZ

/-- Every carrier vertex outside the forced-off region is in its update. -/
theorem status_high_backward {α : Type u} {C L Z Q U : Region α} {D : α → α → Prop}
    (part : StatusPartition C L Z Q) (lc : Sub L C) (qc : Sub Q C) (lu : ∀ x, L x → U x ∨ ∃ y, Parents C D x y ∧ L y)
    (qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y) :
    Sub (fun x => C x ∧ ¬ Z x) (Step C D (StatusMechanism C D L Z Q) U (fun x => C x ∧ ¬ Z x)) := by
  classical
  intro x ⟨hxC, hxNotZ⟩
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
    obtain ⟨q, hqP, hqQ⟩ := qp x hxQ
    apply Or.inr
    refine ⟨hxC, ⟨q, hqP⟩, ?_⟩
    simp only [StatusMechanism, hxL, hxNotZ, ↓reduceIte, SplitGate]
    apply Or.inl
    constructor
    · exact ⟨q, hqP, hqQ, ⟨qc hqQ, fun hz => (part.2.2.2 q) ⟨hz, hqQ⟩⟩, hqP⟩
    · intro y ⟨hyP, hyL⟩
      exact ⟨⟨lc hyL, fun hz => (part.2.1 y) ⟨hyL, hz⟩⟩, hyP⟩


theorem status_two_fixed_points {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) :
    Fixed (Step C D (StatusMechanism C D L Z Q) U) L ∧
    Fixed (Step C D (StatusMechanism C D L Z Q) U) (fun x => C x ∧ ¬ Z x) := by
  classical
  have lc : Sub L C := by intro x hx; exact (part.1 x).mpr (Or.inl hx)
  have zc : Sub Z C := by intro x hx; exact (part.1 x).mpr (Or.inr (Or.inl hx))
  have qc : Sub Q C := by intro x hx; exact (part.1 x).mpr (Or.inr (Or.inr hx))
  have lu : ∀ x, L x → U x ∨ ∃ y, Parents C D x y ∧ L y :=
    fun x hx =>
      match path_last_or_seed (Eq.mpr (congrFun cond.2.2.1 x) hx) with
      | Or.inl hu => Or.inl hu
      | Or.inr ⟨y, hyL, hD⟩ => Or.inr ⟨y, ⟨lc hyL, hD⟩, hyL⟩
  have zp : ∀ x, Z x → (∀ y, ¬ Parents C D x y) ∨ ∃ y, Parents C D x y ∧ Z y :=
    fun x hx =>
      match path_last_or_seed (Eq.mpr (congrFun cond.2.2.2.1 x) hx) with
      | Or.inl ⟨hroot, _⟩ => Or.inl hroot.2
      | Or.inr ⟨y, hyZ, hD⟩ => Or.inr ⟨y, ⟨zc hyZ, hD⟩, hyZ⟩
  have unotz : ∀ x, U x → ¬ Z x :=
    fun x hu hz => (part.2.1 x) ⟨cond.1 hu, hz⟩
  exact ⟨
    funext (fun _x => propext ⟨fun h => status_low_forward part cond.1 zp h,
                                fun h => status_low_backward lc lu h⟩),
    funext (fun _x => propext ⟨fun h => status_high_forward part cond.1 lc unotz zp h,
                                fun h => status_high_backward part lc qc lu cond.2.2.2.2 h⟩)⟩

/-- An OR-gate fixed point contains every internal path from an active root. -/
theorem or_paths_in_fixed {α : Type u} {C L U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (lc : Sub L C)
    (gate : ∀ x, L x → ∀ S, f x S ↔ OrGate (Parents C D x) S)
    (fixed : Fixed (Step C D f U) X) :
    Sub (InternalReach L D U) X := by
  have ux : Sub U X := by
    intro x hu
    have h : Step C D f U X x := Or.inl hu
    rw [fixed] at h
    exact h
  intro x h
  obtain ⟨b, hb, path⟩ := h
  induction path with
  | refl _ => exact ux hb
  | @step y x path hxL edge ih =>
    have hp : Parents C D x y := ⟨lc (path_target path), edge⟩
    have hf : Step C D f U X x :=
      Or.inr ⟨lc hxL, ⟨y, hp⟩, (gate x hxL _).2 (Or.inr ⟨y, hp, ih, hp⟩)⟩
    rw [fixed] at hf
    exact hf

/-- An AND-gate fixed point excludes paths from roots outside the context. -/
theorem and_paths_outside_fixed {α : Type u} {C Z U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (zc : Sub Z C) (unotz : ∀ x, U x → ¬ Z x)
    (gate : ∀ x, Z x → ∀ S, f x S ↔ AndGate (Parents C D x) S)
    (fixed : Fixed (Step C D f U) X) :
    Sub (InternalReach Z D (fun x => Roots C D x ∧ ¬ U x)) (fun x => ¬ X x) := by
  intro x h
  obtain ⟨b, ⟨hbRoot, hbNotU⟩, path⟩ := h
  induction path with
  | refl _ =>
    intro hbX
    have hf : Step C D f U X b := by rw [fixed]; exact hbX
    rcases hf with hu | ⟨_, ⟨p, hp⟩, _⟩
    · exact hbNotU hu
    · exact hbRoot.2 p hp
  | @step y x path hxZ edge ih =>
    intro hxX
    have hp : Parents C D x y := ⟨zc (path_target path), edge⟩
    have hf : Step C D f U X x := by rw [fixed]; exact hxX
    rcases hf with hu | ⟨_, _, hGate⟩
    · exact unotz x hu hxZ
    · exact ih (((gate x hxZ _).1 hGate) y hp).1

theorem status_forces_paths {α : Type u} {C L Z Q U X : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D (StatusMechanism C D L Z Q) U) X) :
    Sub L X ∧ Sub X (fun x => C x ∧ ¬ Z x) := by
  classical
  have lc : Sub L C := fun {x} h => (part.1 x).mpr (Or.inl h)
  have zc : Sub Z C := fun {x} h => (part.1 x).mpr (Or.inr (Or.inl h))
  have unotz : ∀ x, U x → ¬ Z x :=
    fun x hu hz => (part.2.1 x) ⟨cond.1 hu, hz⟩
  have ogate : ∀ x, L x → ∀ S, StatusMechanism C D L Z Q x S ↔ OrGate (Parents C D x) S := by
    intro x hl S
    simp [StatusMechanism, hl]
  have agate : ∀ x, Z x → ∀ S, StatusMechanism C D L Z Q x S ↔ AndGate (Parents C D x) S := by
    intro x hz S
    have hl : ¬ L x := fun h => (part.2.1 x) ⟨h, hz⟩
    simp [StatusMechanism, hl, hz]
  have lpath := or_paths_in_fixed lc ogate fixed
  have zpath := and_paths_outside_fixed zc unotz agate fixed
  have xc : Sub X C :=
    fun {x} hx => (Eq.mpr (congrFun fixed x) hx).elim
      (fun hu => (ctx hu).1) (fun h => h.1)
  exact ⟨
    fun {x} hx => lpath (Eq.mpr (congrFun cond.2.2.1 x) hx),
    fun {x} hx => ⟨xc hx, fun hz => zpath (Eq.mpr (congrFun cond.2.2.2.1 x) hz) hx⟩⟩

/-- The stated OR/AND/split witness is admissible and edge-relevant, with
least fixed point `L` and greatest fixed point the carrier outside `Z`. -/
theorem pattern_witness_extrema {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D)) :
    let f := StatusMechanism C D L Z Q
    Mechanism C D f ∧ Relevant C D f ∧ Least (Step C D f U) = L ∧
      Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x) :=
  let f := StatusMechanism C D L Z Q
  let adm : Mechanism C D f := status_mechanism_admissible part cond.2.2.2.2
  let rel : Relevant C D f := status_mechanism_relevant part cond.2.2.2.2
  let fixes := status_two_fixed_points part cond
  let lowFix := least_fixed (step_monotone adm U)
  let highFix := greatest_fixed (step_monotone adm U)
  let lowForces := status_forces_paths part cond ctx lowFix
  let highForces := status_forces_paths part cond ctx highFix
  ⟨adm, rel,
    funext (fun _x => propext ⟨fun hx => (fixed_bounds fixes.1).1 hx,
                               fun hx => lowForces.1 hx⟩),
    funext (fun _x => propext ⟨fun hx => highForces.2 hx,
                               fun hx => (fixed_bounds fixes.2).2 hx⟩)⟩

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
  have post : Sub Y (F Y) :=
    fun {x} ⟨hxC, hxNotR⟩ =>
      if hxG : G x then
        hm G Y gy (Eq.mpr (congrFun gf x) hxG)
      else
        let hxZ : Z x := ⟨hxC, hxG⟩
        let hxNotU : ¬ U x :=
          fun hu => hxG (Eq.mp (congrFun gf x) (Or.inl hu))
        let hparent : ∃ y, Parents C D x y :=
          Classical.byContradiction (fun hnone =>
            hxNotR ⟨x, ⟨⟨hxC, fun y hy => hnone ⟨y, hy⟩⟩, hxNotU⟩,
              InternalPath.refl x hxZ⟩)
        let noR : ∀ y, Parents C D x y → ¬ R y :=
          fun y hyP hyR =>
            match hyR with
            | ⟨b, hb, path⟩ => hxNotR ⟨b, hb, InternalPath.step path hxZ hyP.2⟩
        let inputs : (fun y => Y y ∧ Parents C D x y) = Parents C D x :=
          funext (fun y => propext ⟨And.right, fun hp => ⟨⟨hp.1, noR y hp⟩, hp⟩⟩)
        Or.inr ⟨hxC, hparent, Eq.mpr (congrArg (f x) inputs) ((adm x hxC).2.2)⟩
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
  let hm : Monotone F := step_monotone adm U
  let lf : Fixed F L := least_fixed hm
  let gf : Fixed F G := greatest_fixed hm
  let lg : Sub L G := (fixed_bounds gf).1
  exact Classical.byContradiction (fun hn =>
    let eq : (fun y => L y ∧ Parents C D x y) = (fun y => G y ∧ Parents C D x y) :=
      funext (fun y => propext ⟨
        fun h => ⟨lg h.1, h.2⟩,
        fun h => ⟨Classical.byContradiction (fun hnot => hn ⟨y, h.2, h.1, hnot⟩), h.2⟩⟩)
    let hfg : F G x := Eq.mpr (congrFun gf x) hxG
    let hfl : F L x := hfg.elim (fun hu => Or.inl hu)
      (fun ⟨hc, hp, hf⟩ => Or.inr ⟨hc, hp, Eq.mpr (congrArg (f x) eq) hf⟩)
    hxNotL (Eq.mp (congrFun lf x) hfl))

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
    clear lf gf zc qc ul rootZ high part
    have h := contextual_least_internal_paths adm ctx
    rw [low] at h
    exact h
  have zpath : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    clear lf gf qc ul rootZ lpath low part
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
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y :=
    fun x hxQ =>
      let hxNotL : ¬ L x := fun hl => (part.2.2.1 x) ⟨hl, hxQ⟩
      let hxNotZ : ¬ Z x := fun hz => (part.2.2.2 x) ⟨hz, hxQ⟩
      let hxG : Greatest F x := Eq.mpr (congrFun high x) ⟨qc hxQ, hxNotZ⟩
      let hxNotLeast : ¬ Least F x :=
        fun h => hxNotL (Eq.mp (congrFun low x) h)
      match ambiguity_has_ambiguous_parent adm ctx hxG hxNotLeast with
      | ⟨y, hyP, hyG, hyNotLeast⟩ =>
        let hyNotL : ¬ L y :=
          fun h => hyNotLeast (Eq.mpr (congrFun low y) h)
        let hyNotZ : ¬ Z y := (Eq.mp (congrFun high y) hyG).2
        let hyQ : Q y :=
          ((part.1 y).mp hyP.1).elim
            (fun h => False.elim (hyNotL h))
            (fun h => h.elim (fun hz => False.elim (hyNotZ hz)) id)
        ⟨y, hyP, hyQ⟩
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
