module
public import DeterminationPatterns.Patterns
@[expose] public section
namespace DeterminationPatterns
universe u

/-- The carrier is exactly the disjoint union of the three statuses. -/
def StatusPartition {α : Type u} (C L Z Q : Region α) : Prop :=
  (∀ x, C x ↔ L x ∨ Z x ∨ Q x) ∧
  (∀ x, ¬ (L x ∧ Z x)) ∧ (∀ x, ¬ (L x ∧ Q x)) ∧ (∀ x, ¬ (Z x ∧ Q x))

/-- The exact path, root, and ambiguous-parent conditions in the source. -/
def PatternConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (U L Z Q : Region α) : Prop :=
  Sub U L ∧ Sub (fun x => Roots C D x ∧ ¬ U x) Z ∧
  InternalReach L D U = L ∧
  InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z ∧
  (∀ x, Q x → ∃ y, Parents C D x y ∧ Q y)

def OrGate {α : Type u} (P S : Region α) : Prop :=
  (∀ y, ¬ P y) ∨ ∃ y, P y ∧ S y

def AndGate {α : Type u} (P S : Region α) : Prop := ∀ y, P y → S y

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
