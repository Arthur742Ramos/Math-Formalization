module
import Init
@[expose] public section

/-! The explicit pattern witness is admissible and edge-relevant. -/
namespace DeterminationPatterns
universe u

/-- A region is a predicate on the ambient type. -/
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

/-- The carrier is exactly the disjoint union of L, Z and Q. -/
def StatusPartition {α : Type u} (C L Z Q : Region α) : Prop :=
  (∀ x, C x ↔ L x ∨ Z x ∨ Q x) ∧
  (∀ x, ¬ (L x ∧ Z x)) ∧ (∀ x, ¬ (L x ∧ Q x)) ∧ (∀ x, ¬ (Z x ∧ Q x))

/-- The OR gate fires on an active parent and is true when there are no parents. -/
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

/-- The witness is admissible when the statuses partition the carrier and
every ambiguous vertex has an ambiguous parent. -/
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

/-- Under the same assumptions every listed carrier edge is relevant. -/
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


end DeterminationPatterns
