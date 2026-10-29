module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for the copy-majority representation example. -/
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


/-- `X` is unchanged by `F`. -/
def Fixed {α : Type u} (F : Region α → Region α) (X : Region α) : Prop := F X = X

end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- At least two of the three Boolean-valued propositions hold. -/
def Majority (a b c : Prop) : Prop := (a ∧ b) ∨ (a ∧ c) ∨ (b ∧ c)

theorem majority_copy (a b : Prop) : Majority a a b ↔ a := by
  constructor
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  · intro ha; exact Or.inl ⟨ha, ha⟩

theorem majority_opposite (a : Prop) : Majority False True a ↔ a := by
  simp [Majority]

/-- At indices in `I` use prescribed values `w`; elsewhere use `u`. -/
noncomputable def Clamp (I w u : Region Nat) (n : Nat) : Prop := by
  classical
  exact if I n then w n else u n

/-- The original link assignment copies the source except at clamped links. -/
def ProjectionSolution (u I w a : Region Nat) : Prop := ∀ n, a n ↔ Clamp I w u n

/-- Copies equal sources; links use majority except where replaced by clamps. -/
def ExpandedSolution (u I w c a : Region Nat) : Prop :=
  (∀ n, c n ↔ u n) ∧
  (∀ n, a n ↔ Clamp I w (fun n => Majority (u n) (c n) (a (n+1))) n)

/-- With arbitrary original-link clamps, expanded solutions are exactly
the projection solutions together with copies equal to sources. -/
theorem expanded_projection_iff (u I w c a : Region Nat) :
    ExpandedSolution u I w c a ↔ c = u ∧ ProjectionSolution u I w a := by
  classical
  constructor
  · rintro ⟨hc, ha⟩
    have ceq : c = u := by funext n; exact propext (hc n)
    refine ⟨ceq, ?_⟩
    intro n
    have hn := ha n
    rw [ceq] at hn
    by_cases hi : I n
    · simpa [Clamp, hi] using hn
    · simpa [Clamp, hi, majority_copy] using hn
  · rintro ⟨rfl, ha⟩
    refine ⟨fun _ => Iff.rfl, ?_⟩
    intro n
    have hn := ha n
    by_cases hi : I n
    · simpa [Clamp, hi] using hn
    · simpa [Clamp, hi, majority_copy] using hn

/-- Existential filtering by any observation on retained source/link values
agrees between the expanded and projection solutions. -/
theorem projection_observation_preservation (u I w : Region Nat)
    (Obs : Region Nat → Region Nat → Prop) :
    (∃ c a, ExpandedSolution u I w c a ∧ Obs u a) ↔
      ∃ a, ProjectionSolution u I w a ∧ Obs u a := by
  constructor
  · rintro ⟨c, a, h, obs⟩
    exact ⟨a, (expanded_projection_iff u I w c a).mp h |>.2, obs⟩
  · rintro ⟨a, h, obs⟩
    exact ⟨u, a, (expanded_projection_iff u I w u a).mpr ⟨rfl, h⟩, obs⟩

/-- Universal observation properties on retained values agree between the
expanded and projection solutions. -/
theorem every_projection_observation_preserved (u I w : Region Nat)
    (Obs : Region Nat → Region Nat → Prop) :
    (∀ c a, ExpandedSolution u I w c a → Obs u a) ↔
      ∀ a, ProjectionSolution u I w a → Obs u a := by
  constructor
  · intro h a ha
    exact h u a ((expanded_projection_iff u I w u a).mpr ⟨rfl, ha⟩)
  · intro h c a ha
    exact h a ((expanded_projection_iff u I w c a).mp ha).2

/-- Copies use prescribed values at `J` and otherwise copy sources; links
retain their majority equations. -/
def CopiesClampedSolution (u J z c a : Region Nat) : Prop :=
  (∀ n, c n ↔ Clamp J z u n) ∧
  (∀ n, a n ↔ Majority (u n) (c n) (a (n+1)))

/-- Clamping all copies on with all sources off admits two different link
solutions; the intervention may be infinite. -/
theorem copy_interventions_nonunique :
    ∃ c a b : Region Nat,
      CopiesClampedSolution (fun _ => False) (fun _ => True) (fun _ => True) c a ∧
      CopiesClampedSolution (fun _ => False) (fun _ => True) (fun _ => True) c b ∧ a ≠ b := by
  classical
  refine ⟨(fun _ => True), (fun _ => False), (fun _ => True), ?_, ?_, ?_⟩
  · constructor <;> intro n <;> simp [Clamp, Majority]
  · constructor <;> intro n <;> simp [Clamp, Majority]
  · intro h
    have h0 := congrFun h 0
    exact Eq.mp h0.symm True.intro

/-- The expanded carrier consists of source, copy and link vertices. -/
inductive CopyNode where
  | root : Nat → CopyNode
  | copy : Nat → CopyNode
  | link : Nat → CopyNode
  deriving DecidableEq

/-- Each copy depends on its source; each link depends on source, copy and
next link; sources have no parents. -/
def CopyDependency (y x : CopyNode) : Prop :=
  match x with
  | .root _ => False
  | .copy n => y = .root n
  | .link n => y = .root n ∨ y = .copy n ∨ y = .link (n+1)

/-- Copies read their source and links use the three-input majority rule. -/
def CopyMechanism (x : CopyNode) (S : Region CopyNode) : Prop :=
  match x with
  | .root _ => True
  | .copy n => S (.root n)
  | .link n => Majority (S (.root n)) (S (.copy n)) (S (.link (n+1)))

/-- Combine source, copy and link assignments on the expanded carrier. -/
def CopyState (u c a : Region Nat) : Region CopyNode := fun x =>
  match x with
  | .root n => u n
  | .copy n => c n
  | .link n => a n

/-- Select the active sources and no copy or link vertices. -/
def CopyContext (u : Region Nat) : Region CopyNode := fun x =>
  match x with
  | .root n => u n
  | .copy _ => False
  | .link _ => False

@[simp] theorem copy_step_root (u : Region Nat) (X : Region CopyNode) (n : Nat) :
    Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u) X (.root n) ↔ u n := by
  simp [Step, CopyContext, Parents, CopyDependency]

@[simp] theorem copy_step_copy (u : Region Nat) (X : Region CopyNode) (n : Nat) :
    Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u) X (.copy n) ↔ X (.root n) := by
  simp [Step, CopyContext, Parents, CopyDependency, CopyMechanism]

@[simp] theorem copy_step_link (u : Region Nat) (X : Region CopyNode) (n : Nat) :
    Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u) X (.link n) ↔
      Majority (X (.root n)) (X (.copy n)) (X (.link (n+1))) := by
  simp [Step, CopyContext, Parents, CopyDependency, CopyMechanism]

theorem copy_fixed_iff (u : Region Nat) (X : Region CopyNode) :
    Fixed (Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u)) X ↔
      X = CopyState u u u := by
  constructor
  · intro fixed
    have roots : ∀ n, X (.root n) ↔ u n := by
      intro n
      have h := congrFun fixed (.root n)
      exact (Iff.of_eq h).symm.trans (copy_step_root u X n)
    have copies : ∀ n, X (.copy n) ↔ u n := by
      intro n
      have h := congrFun fixed (.copy n)
      exact (Iff.of_eq h).symm.trans ((copy_step_copy u X n).trans (roots n))
    have links : ∀ n, X (.link n) ↔ u n := by
      intro n
      have h := (Iff.of_eq (congrFun fixed (.link n))).symm.trans (copy_step_link u X n)
      rw [propext (roots n), propext (copies n)] at h
      exact h.trans (majority_copy (u n) (X (.link (n+1))))
    funext x
    apply propext
    cases x with
    | root n => exact roots n
    | copy n => exact copies n
    | link n => exact links n
  · intro h
    rw [h]
    funext x
    apply propext
    cases x with
    | root n => simp [CopyState]
    | copy n => simp [CopyState]
    | link n => simp [CopyState, majority_copy]

/-- The operator has a fixed region and every fixed region equals it. -/
def UniqueFixed {α : Type u} (F : Region α → Region α) : Prop :=
  ∃ X, Fixed F X ∧ ∀ Y, Fixed F Y → Y = X

/-- The mechanism has exactly one fixed solution at every legal context. -/
def ContextDeterminate {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ U, Sub U (Roots C D) → UniqueFixed (Step C D f U)

theorem copy_roots_are_roots (n : Nat) : Roots (fun _ => True) CopyDependency (.root n) := by
  simp [Roots, Parents, CopyDependency]

theorem legal_copy_context (U : Region CopyNode)
    (hU : Sub U (Roots (fun _ => True) CopyDependency)) :
    U = CopyContext (fun n => U (.root n)) := by
  funext x
  apply propext
  cases x with
  | root n => exact Iff.rfl
  | copy n =>
    constructor
    · intro h
      have hr := hU h
      exact hr.2 (.root n) ⟨True.intro, rfl⟩
    · intro h; exact False.elim h
  | link n =>
    constructor
    · intro h
      have hr := hU h
      exact hr.2 (.root n) ⟨True.intro, Or.inl rfl⟩
    · intro h; exact False.elim h

theorem copy_majority_context_unique (u : Region Nat) :
    UniqueFixed (Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u)) := by
  refine ⟨CopyState u u u, (copy_fixed_iff u _).mpr rfl, ?_⟩
  intro Y hY
  exact (copy_fixed_iff u Y).mp hY

/-- The copy-majority system has one solution at every root context. -/
theorem copy_majority_all_contexts :
    ContextDeterminate (fun _ => True) CopyDependency CopyMechanism := by
  intro U hU
  rw [legal_copy_context U hU]
  exact copy_majority_context_unique _

/-- Replaces exactly the original link equations indexed by I. -/
noncomputable def OriginalIntervention (u I w : Region Nat) (X : Region CopyNode) : Region CopyNode :=
  fun x => match x with
  | .root n => u n
  | .copy n => X (.root n)
  | .link n => Clamp I w (fun k => Majority (X (.root k)) (X (.copy k)) (X (.link (k+1))) ) n

theorem original_link_intervention_fixed_iff (u I w : Region Nat) (X : Region CopyNode) :
    Fixed (OriginalIntervention u I w) X ↔ X = CopyState u u (Clamp I w u) := by
  classical
  constructor
  · intro fixed
    have roots : ∀ n, X (.root n) ↔ u n := by
      intro n
      exact (Iff.of_eq (congrFun fixed (.root n))).symm
    have copies : ∀ n, X (.copy n) ↔ u n := by
      intro n
      exact (Iff.of_eq (congrFun fixed (.copy n))).symm.trans (roots n)
    have links : ∀ n, X (.link n) ↔ Clamp I w u n := by
      intro n
      have h := (Iff.of_eq (congrFun fixed (.link n))).symm
      change X (.link n) ↔ Clamp I w (fun k => Majority (X (.root k)) (X (.copy k)) (X (.link (k+1)))) n at h
      by_cases hi : I n
      · simpa [Clamp, hi] using h
      · simp only [Clamp, hi, ↓reduceIte] at h ⊢
        rw [propext (roots n), propext (copies n)] at h
        exact h.trans (majority_copy (u n) (X (.link (n+1))))
    funext x
    apply propext
    cases x with
    | root n => exact roots n
    | copy n => exact copies n
    | link n => exact links n
  · intro h
    rw [h]
    funext x
    apply propext
    cases x with
    | root n => exact Iff.rfl
    | copy n => exact Iff.rfl
    | link n =>
      by_cases hi : I n
      · simp [OriginalIntervention, CopyState, Clamp, hi]
      · simp [OriginalIntervention, CopyState, Clamp, hi, majority_copy]

/-- Arbitrary hard interventions on original links preserve unique solutions. -/
theorem original_link_interventions_unique (u I w : Region Nat) :
    UniqueFixed (OriginalIntervention u I w) := by
  refine ⟨CopyState u u (Clamp I w u), (original_link_intervention_fixed_iff u I w _).mpr rfl, ?_⟩
  intro X hx
  exact (original_link_intervention_fixed_iff u I w X).mp hx

theorem copy_state_injective (u c a d b : Region Nat) :
    CopyState u c a = CopyState u d b ↔ c = d ∧ a = b := by
  constructor
  · intro h
    constructor
    · funext n; exact congrFun h (.copy n)
    · funext n; exact congrFun h (.link n)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Full-carrier fixed solutions of original-link interventions are exactly
the specified expanded copy/link solutions. -/
theorem carrier_expanded_solution_bridge (u I w c a : Region Nat) :
    Fixed (OriginalIntervention u I w) (CopyState u c a) ↔ ExpandedSolution u I w c a := by
  rw [original_link_intervention_fixed_iff, copy_state_injective, expanded_projection_iff]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, fun _ => Iff.rfl⟩
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    funext n
    exact propext (h n)

/-- The expanded mechanism is normalized and monotone. -/
theorem copy_majority_admissible :
    Mechanism (fun _ => True) CopyDependency CopyMechanism := by
  intro x _
  cases x with
  | root n =>
    simp [CopyMechanism, Parents, CopyDependency]
  | copy n =>
    constructor
    · intro A B hAB h
      exact hAB h
    constructor
    · constructor
      · intro h; exact False.elim h
      · intro h; exact False.elim (h (.root n) ⟨True.intro, rfl⟩)
    · exact ⟨True.intro, rfl⟩
  | link n =>
    constructor
    · intro A B hAB h
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨hAB ha, hAB hb⟩
      · exact Or.inr (Or.inl ⟨hAB ha, hAB hb⟩)
      · exact Or.inr (Or.inr ⟨hAB ha, hAB hb⟩)
    constructor
    · constructor
      · intro h
        rcases h with ⟨bad, _⟩ | ⟨bad, _⟩ | ⟨bad, _⟩ <;> exact False.elim bad
      · intro h
        exact False.elim (h (.root n) ⟨True.intro, Or.inl rfl⟩)
    · exact Or.inl ⟨⟨True.intro, Or.inl rfl⟩, ⟨True.intro, Or.inr (Or.inl rfl)⟩⟩

theorem no_link_intervention_is_contextual (u w : Region Nat) :
    OriginalIntervention u (fun _ => False) w =
      Step (fun _ => True) CopyDependency CopyMechanism (CopyContext u) := by
  classical
  funext X x
  apply propext
  cases x with
  | root n => simp [OriginalIntervention]
  | copy n => simp [OriginalIntervention]
  | link n => simp [OriginalIntervention, Clamp]

/-- Every listed edge of the expanded mechanism is functionally relevant. -/
theorem copy_majority_relevant :
    Relevant (fun _ => True) CopyDependency CopyMechanism := by
  intro x _ y hy
  cases x with
  | root n => exact False.elim hy.2
  | copy n =>
    have eq : y = .root n := hy.2
    subst y
    refine ⟨(fun _ => False), ?_, ?_, ?_⟩
    · intro z hz; exact False.elim hz
    · simp [CopyMechanism]
    · simp [CopyMechanism]
  | link n =>
    rcases hy.2 with eq | eq | eq
    · subst y
      refine ⟨(fun z => z = .copy n), ?_, ?_, ?_⟩
      · intro z hz
        subst z
        simp [Parents, CopyDependency]
      · simp [CopyMechanism, Majority]
      · simp [CopyMechanism, Majority]
    · subst y
      refine ⟨(fun z => z = .root n), ?_, ?_, ?_⟩
      · intro z hz
        subst z
        simp [Parents, CopyDependency]
      · simp [CopyMechanism, Majority]
      · simp [CopyMechanism, Majority]
    · subst y
      refine ⟨(fun z => z = .root n), ?_, ?_, ?_⟩
      · intro z hz
        subst z
        simp [Parents, CopyDependency]
      · simp [CopyMechanism, Majority]
      · simp [CopyMechanism, Majority]

/-- The all-copies-on, all-sources-off intervention is not uniquely solvable. -/
theorem copy_interventions_not_unique :
    ¬ (∃ v : Region Nat × Region Nat,
      CopiesClampedSolution (fun _ => False) (fun _ => True) (fun _ => True) v.1 v.2 ∧
      ∀ w : Region Nat × Region Nat,
        CopiesClampedSolution (fun _ => False) (fun _ => True) (fun _ => True) w.1 w.2 → w = v) := by
  rintro ⟨v, _, unique⟩
  obtain ⟨c, a, b, ha, hb, hne⟩ := copy_interventions_nonunique
  have h1 := unique (c, a) ha
  have h2 := unique (c, b) hb
  have eq : a = b := congrArg Prod.snd (h1.trans h2.symm)
  exact hne eq

end DeterminationPatterns
