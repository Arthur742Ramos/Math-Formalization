module
public import DeterminationPatterns.TargetScope
@[expose] public section
namespace DeterminationPatterns
universe u

/-- Paper-style local rules: at a nonroot the rule is monotone on parent
subsets, rejects the empty set, and accepts the full parent set. Values at
roots and on non-parent inputs are immaterial. -/
def LocalMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x → (∃ y, Parents C D x y) →
    (∀ A B, Sub A (Parents C D x) → Sub B (Parents C D x) →
      Sub A B → f x A → f x B) ∧
    ¬ f x (fun _ => False) ∧ f x (Parents C D x)

/-- The parent-restricted rule is extended to every ambient input, with a
canonical true root entry. -/
noncomputable def ExtendLocalMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (x : α) (S : Region α) : Prop := by
  classical
  exact if ∃ y, Parents C D x y then f x (fun y => S y ∧ Parents C D x y) else True

theorem parent_intersection_self {α : Type u} {P S : Region α} (h : Sub S P) :
    (fun x => S x ∧ P x) = S := by
  funext x
  exact propext ⟨fun hx => hx.1, fun hx => ⟨hx, h hx⟩⟩

/-- Extension of paper-local rules is a globally monotone normalized mechanism. -/
theorem extend_local_mechanism {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (hlocal : LocalMechanism C D f) :
    Mechanism C D (ExtendLocalMechanism C D f) := by
  classical
  intro x hc
  by_cases hp : ∃ y, Parents C D x y
  · have rule := hlocal x hc hp
    refine ⟨?_, ?_, ?_⟩
    · intro A B hAB hA
      simp only [ExtendLocalMechanism, ite_eq_left hp] at hA ⊢
      exact rule.1 _ _ (fun _ h => h.2) (fun _ h => h.2)
        (fun _ h => ⟨hAB h.1, h.2⟩) hA
    · simp only [ExtendLocalMechanism, ite_eq_left hp]
      rw [parent_intersection_self (show Sub (fun _ => False) (Parents C D x) from fun _ h => h.elim)]
      constructor
      · intro h; exact False.elim (rule.2.1 h)
      · intro hn; obtain ⟨y, hy⟩ := hp; exact False.elim (hn y hy)
    · simp only [ExtendLocalMechanism, ite_eq_left hp]
      rw [parent_intersection_self (show Sub (Parents C D x) (Parents C D x) from fun _ h => h)]
      exact rule.2.2
  · refine ⟨?_, ?_, ?_⟩
    · intro A B _ _; simp [ExtendLocalMechanism, hp]
    · simp only [ExtendLocalMechanism, ite_eq_right hp, true_iff]
      intro y hy
      exact hp ⟨y, hy⟩
    · simp [ExtendLocalMechanism, hp]

/-- Extension preserves functional relevance exactly, since each relevance
witness and its one-parent enlargement lie within the parent set. -/
theorem extend_local_relevant_iff {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} :
    Relevant C D (ExtendLocalMechanism C D f) ↔ Relevant C D f := by
  classical
  unfold Relevant
  constructor <;> intro rel x hc y hy
  all_goals
    have hp : ∃ z, Parents C D x z := ⟨y, hy⟩
    obtain ⟨S, sub, no, yes⟩ := rel x hc y hy
    have subS : Sub S (Parents C D x) := fun _ h => (sub h).1
    have subY : Sub (fun z => z = y ∨ S z) (Parents C D x) := by
      intro z hz
      rcases hz with rfl | hz
      · exact hy
      · exact subS hz
    refine ⟨S, sub, ?_, ?_⟩
    · simpa only [ExtendLocalMechanism, ite_eq_left hp, parent_intersection_self subS] using no
    · simpa only [ExtendLocalMechanism, ite_eq_left hp, parent_intersection_self subY] using yes

/-- The contextual operator is unchanged by extending the local rules. -/
theorem extend_local_step {α : Type u} {C U X : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} :
    Step C D (ExtendLocalMechanism C D f) U X = Step C D f U X := by
  classical
  funext x
  apply propext
  constructor <;> intro h
  all_goals
    rcases h with hu | ⟨hc, hp, hf⟩
    · exact Or.inl hu
    · right
      refine ⟨hc, hp, ?_⟩
      have sub : Sub (fun y => X y ∧ Parents C D x y) (Parents C D x) := fun _ h => h.2
      simpa only [ExtendLocalMechanism, ite_eq_left hp, parent_intersection_self sub] using hf


/-- The literal paper input domain at `x`: subsets of its parent set. -/
def ParentInput {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) :=
  {S : Region α // Sub S (Parents C D x)}

def emptyParentInput {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) :
    ParentInput C D x := ⟨fun _ => False, fun _ h => h.elim⟩

def fullParentInput {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) :
    ParentInput C D x := ⟨Parents C D x, fun _ h => h⟩

/-- Paper-local monotonicity and normalization, stated on the subtype of
parent subsets. The family may have arbitrary root entries, which are ignored. -/
def PaperMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (g : (x : α) → ParentInput C D x → Prop) : Prop :=
  ∀ x, C x → (∃ y, Parents C D x y) →
    (∀ A B : ParentInput C D x, Sub A.val B.val → g x A → g x B) ∧
    ¬ g x (emptyParentInput C D x) ∧ g x (fullParentInput C D x)

/-- Interpret a paper rule on an arbitrary ambient input by intersecting it
with the parent set. -/
def PaperRaw {α : Type u} (C : Region α) (D : α → α → Prop)
    (g : (x : α) → ParentInput C D x → Prop) (x : α) (S : Region α) : Prop :=
  g x ⟨fun y => S y ∧ Parents C D x y, fun _ h => h.2⟩

theorem paper_raw_local {α : Type u} {C : Region α} {D : α → α → Prop}
    {g : (x : α) → ParentInput C D x → Prop} (paper : PaperMechanism C D g) :
    LocalMechanism C D (PaperRaw C D g) := by
  intro x hc hp
  have rule := paper x hc hp
  refine ⟨?_, ?_, ?_⟩
  · intro A B _ _ hAB hA
    let A1 : ParentInput C D x := ⟨fun y => A y ∧ Parents C D x y, fun _ h => h.2⟩
    let B1 : ParentInput C D x := ⟨fun y => B y ∧ Parents C D x y, fun _ h => h.2⟩
    change g x A1 at hA
    change g x B1
    exact rule.1 A1 B1 (fun _ h => ⟨hAB h.1, h.2⟩) hA
  · have eq : (⟨(fun y => False ∧ Parents C D x y), fun _ h => h.2⟩ : ParentInput C D x) =
        emptyParentInput C D x := by
      apply Subtype.ext
      funext y
      exact propext ⟨fun h => h.1, fun h => h.elim⟩
    simpa only [PaperRaw, eq] using rule.2.1
  · have eq : (⟨(fun y => Parents C D x y ∧ Parents C D x y), fun _ h => h.2⟩ : ParentInput C D x) =
        fullParentInput C D x := by
      apply Subtype.ext
      funext y
      exact propext ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
    simpa only [PaperRaw, eq] using rule.2.2

/-- Every paper-local mechanism has a total normalized extension. -/
theorem paper_mechanism_has_total_extension {α : Type u} {C : Region α}
    {D : α → α → Prop} {g : (x : α) → ParentInput C D x → Prop}
    (paper : PaperMechanism C D g) :
    Mechanism C D (ExtendLocalMechanism C D (PaperRaw C D g)) :=
  extend_local_mechanism (paper_raw_local paper)

/-- On a parent subset, the paper rule and its ambient interpretation agree. -/
theorem paper_raw_on_parent_input {α : Type u} {C : Region α}
    {D : α → α → Prop} (g : (x : α) → ParentInput C D x → Prop)
    (x : α) (S : ParentInput C D x) : PaperRaw C D g x S.val ↔ g x S := by
  have eq : (⟨(fun y => S.val y ∧ Parents C D x y), fun _ h => h.2⟩ : ParentInput C D x) = S := by
    apply Subtype.ext
    exact parent_intersection_self S.property
  simp only [PaperRaw, eq]


/-- Restricting an ambient rule to the parent-subset domain recovers a
paper-local mechanism whenever the original mechanism is admissible. -/
def RestrictToParents {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (x : α) (S : ParentInput C D x) : Prop := f x S.val

theorem total_mechanism_restricts_to_paper {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} (adm : Mechanism C D f) :
    PaperMechanism C D (RestrictToParents C D f) := by
  intro x hc hp
  refine ⟨?_, ?_, ?_⟩
  · intro A B sub h
    exact (adm x hc).1 A.val B.val sub h
  · intro h
    have no := (adm x hc).2.1.mp h
    obtain ⟨y, hy⟩ := hp
    exact no y hy
  · exact (adm x hc).2.2


/-- Add an existing parent to a parent-subset input. -/
def addParent {α : Type u} {C : Region α} {D : α → α → Prop} {x y : α}
    (hy : Parents C D x y) (S : ParentInput C D x) : ParentInput C D x :=
  ⟨fun z => z = y ∨ S.val z, by
    intro z hz
    rcases hz with rfl | hz
    · exact hy
    · exact S.property hz⟩

/-- Relevance expressed directly on paper-style parent-subset inputs. -/
def PaperRelevant {α : Type u} (C : Region α) (D : α → α → Prop)
    (g : (x : α) → ParentInput C D x → Prop) : Prop :=
  ∀ x, C x → ∀ y, (hy : Parents C D x y) →
    ∃ S : ParentInput C D x,
      Sub S.val (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ g x S ∧ g x (addParent hy S)

/-- Paper-domain relevance is exactly relevance of the ambient extension. -/
theorem paper_relevance_iff_total {α : Type u} {C : Region α} {D : α → α → Prop}
    {g : (x : α) → ParentInput C D x → Prop} :
    PaperRelevant C D g ↔ Relevant C D (ExtendLocalMechanism C D (PaperRaw C D g)) := by
  rw [extend_local_relevant_iff]
  constructor
  · intro rel x hc y hy
    obtain ⟨S, sub, no, yes⟩ := rel x hc y hy
    refine ⟨S.val, sub, ?_, ?_⟩
    · simpa only [paper_raw_on_parent_input] using no
    · change PaperRaw C D g x (addParent hy S).val
      exact (paper_raw_on_parent_input g x (addParent hy S)).mpr yes
  · intro rel x hc y hy
    obtain ⟨S, sub, no, yes⟩ := rel x hc y hy
    let S1 : ParentInput C D x := ⟨S, fun _ h => (sub h).1⟩
    refine ⟨S1, sub, ?_, ?_⟩
    · intro h
      exact no ((paper_raw_on_parent_input g x S1).mpr h)
    · exact (paper_raw_on_parent_input g x (addParent hy S1)).mp yes

/-- The contextual operator stated directly using parent-subset inputs. -/
def PaperStep {α : Type u} (C : Region α) (D : α → α → Prop)
    (g : (x : α) → ParentInput C D x → Prop) (U X : Region α) : Region α :=
  fun x => U x ∨ (C x ∧ (∃ y, Parents C D x y) ∧
    g x ⟨fun y => X y ∧ Parents C D x y, fun _ h => h.2⟩)

/-- The total extension induces exactly the paper contextual operator. -/
theorem paper_step_iff_total {α : Type u} {C U X : Region α} {D : α → α → Prop}
    {g : (x : α) → ParentInput C D x → Prop} :
    Step C D (ExtendLocalMechanism C D (PaperRaw C D g)) U X = PaperStep C D g U X := by
  rw [extend_local_step]
  funext x
  apply propext
  constructor <;> intro h
  all_goals
    rcases h with hu | ⟨hc, hp, hg⟩
    · exact Or.inl hu
    · right
      refine ⟨hc, hp, ?_⟩
      let S : ParentInput C D x := ⟨fun y => X y ∧ Parents C D x y, fun _ h => h.2⟩
      first
      | exact (paper_raw_on_parent_input g x S).mp hg
      | exact (paper_raw_on_parent_input g x S).mpr hg


/-- Restricting a total rule preserves the contextual operator exactly. -/
theorem paper_restriction_preserves_step {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} :
    PaperStep C D (RestrictToParents C D f) U X = Step C D f U X := rfl

/-- Restricting a total rule preserves relevance, since the relevance
witnesses only query subsets of the parent set. -/
theorem paper_restriction_preserves_relevance {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} :
    PaperRelevant C D (RestrictToParents C D f) ↔ Relevant C D f := by
  constructor
  · intro rel x hc y hy
    obtain ⟨S, sub, no, yes⟩ := rel x hc y hy
    exact ⟨S.val, sub, no, yes⟩
  · intro rel x hc y hy
    obtain ⟨S, sub, no, yes⟩ := rel x hc y hy
    let S1 : ParentInput C D x := ⟨S, fun _ h => (sub h).1⟩
    exact ⟨S1, sub, no, yes⟩

end DeterminationPatterns
