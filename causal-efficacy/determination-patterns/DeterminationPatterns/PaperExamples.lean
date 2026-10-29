module
public import DeterminationPatterns.RepresentationBridge
public import DeterminationPatterns.SourceInference
public import DeterminationPatterns.CopyMajority
@[expose] public section

/-! Explicit specializations of the manuscript's observation and shared-source examples. -/
namespace DeterminationPatterns

def RootlessCopyDependency (y x : Nat) : Prop := y = x + 1

def RootlessCopyMechanism (x : Nat) (S : Region Nat) : Prop := S (x + 1)

def CopyEquation (X : Region Nat) : Prop := ∀ n, X n ↔ X (n + 1)

theorem rootless_copy_no_roots (x : Nat) :
    ¬ Roots (fun _ => True) RootlessCopyDependency x := by
  intro root
  exact root.2 (x + 1) ⟨True.intro, rfl⟩

theorem rootless_copy_admissible :
    Mechanism (fun _ => True) RootlessCopyDependency RootlessCopyMechanism := by
  intro x _
  refine ⟨?_, ?_, ?_⟩
  · intro A B sub ha
    exact sub ha
  · constructor
    · intro h
      exact False.elim h
    · intro none
      exact False.elim (none (x + 1) ⟨True.intro, rfl⟩)
  · exact ⟨True.intro, rfl⟩

theorem rootless_copy_relevant :
    Relevant (fun _ => True) RootlessCopyDependency RootlessCopyMechanism := by
  intro x _ y parent
  have eq : y = x + 1 := parent.2
  subst y
  refine ⟨fun _ => False, ?_, ?_, ?_⟩
  · intro z hz
    exact False.elim hz
  · simp [RootlessCopyMechanism]
  · simp [RootlessCopyMechanism]

theorem rootless_copy_step (X : Region Nat) (n : Nat) :
    Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
      (fun _ => False) X n ↔ X (n + 1) := by
  simp [Step, Parents, RootlessCopyDependency, RootlessCopyMechanism]

theorem copy_equation_iff_constants (X : Region Nat) :
    CopyEquation X ↔ X = (fun _ => False) ∨ X = (fun _ => True) := by
  classical
  constructor
  · intro h
    have same : ∀ n, X n ↔ X 0 := by
      intro n
      induction n with
      | zero => exact Iff.rfl
      | succ n ih => exact (h n).symm.trans ih
    by_cases h0 : X 0
    · right
      funext n
      exact propext ⟨fun _ => True.intro, fun _ => (same n).mpr h0⟩
    · left
      funext n
      exact propext ⟨fun hn => h0 ((same n).mp hn), False.elim⟩
  · rintro (rfl | rfl) <;> simp [CopyEquation]

theorem rootless_fixed_iff_copy (X : Region Nat) :
    Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
      (fun _ => False)) X ↔ CopyEquation X := by
  constructor
  · intro h n
    exact (Iff.of_eq (congrFun h n)).symm.trans (rootless_copy_step X n)
  · intro h
    funext n
    exact propext ((rootless_copy_step X n).trans (h n).symm)

theorem rootless_fixed_iff_constants (X : Region Nat) :
    Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
      (fun _ => False)) X ↔ X = (fun _ => False) ∨ X = (fun _ => True) :=
  (rootless_fixed_iff_copy X).trans (copy_equation_iff_constants X)

theorem rootless_observed_iff_all_on (X : Region Nat) :
    (Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
      (fun _ => False)) X ∧ X 0) ↔ X = (fun _ => True) := by
  constructor
  · rintro ⟨fixed, observed⟩
    rcases (rootless_fixed_iff_constants X).mp fixed with off | on
    · rw [off] at observed
      exact False.elim observed
    · exact on
  · intro on
    subst X
    exact ⟨(rootless_fixed_iff_constants _).mpr (Or.inr rfl), True.intro⟩

theorem rootless_observed_unique :
    ∃ X : Region Nat,
      (Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
        (fun _ => False)) X ∧ X 0) ∧
      ∀ Y, (Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
        (fun _ => False)) Y ∧ Y 0) → Y = X := by
  refine ⟨fun _ => True, (rootless_observed_iff_all_on _).mpr rfl, ?_⟩
  intro Y h
  exact (rootless_observed_iff_all_on Y).mp h

theorem rootless_unconditioned_not_unique :
    ¬ ∃ X : Region Nat,
      Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
        (fun _ => False)) X ∧
      ∀ Y, Fixed (Step (fun _ => True) RootlessCopyDependency RootlessCopyMechanism
        (fun _ => False)) Y → Y = X := by
  rintro ⟨X, _, unique⟩
  have e := (unique (fun _ => False) ((rootless_fixed_iff_constants _).mpr (Or.inl rfl))).trans
    (unique (fun _ => True) ((rootless_fixed_iff_constants _).mpr (Or.inr rfl))).symm
  have absurd := congrFun e 0
  exact Eq.mpr absurd True.intro

/-- These four cases fix the shared source value; no observation replaces an equation. -/
def FigureLabel : Nat → Unit := fun _ => ()
def FigureGate (g : Bool) : Nat → Bool := fun _ => g
def FigureContext (b : Bool) : Unit → Bool := fun _ => b

theorem figure_and_off (v : Region Nat) :
    SpineSolution FigureLabel (FigureGate false) (FigureContext false) v ↔ v = (fun _ => False) := by
  constructor
  · intro h
    funext n
    exact propext ⟨fun hv => by simpa [SpineSolution, FigureGate, FigureContext, SpineGate] using (h n).mp hv, False.elim⟩
  · rintro rfl
    simp [SpineSolution, FigureGate, FigureContext, SpineGate]

theorem figure_or_on (v : Region Nat) :
    SpineSolution FigureLabel (FigureGate true) (FigureContext true) v ↔ v = (fun _ => True) := by
  constructor
  · intro h
    funext n
    exact propext ⟨fun _ => True.intro, fun _ => (h n).mpr (by simp [FigureGate, FigureContext, SpineGate])⟩
  · rintro rfl
    simp [SpineSolution, FigureGate, FigureContext, SpineGate]

theorem figure_and_on (v : Region Nat) :
    SpineSolution FigureLabel (FigureGate false) (FigureContext true) v ↔
      v = (fun _ => False) ∨ v = (fun _ => True) := by
  apply Iff.trans ?_ (copy_equation_iff_constants v)
  simp [SpineSolution, FigureGate, FigureContext, SpineGate, CopyEquation]

theorem figure_or_off (v : Region Nat) :
    SpineSolution FigureLabel (FigureGate true) (FigureContext false) v ↔
      v = (fun _ => False) ∨ v = (fun _ => True) := by
  apply Iff.trans ?_ (copy_equation_iff_constants v)
  simp [SpineSolution, FigureGate, FigureContext, SpineGate, CopyEquation]

theorem figure_and_off_observation_impossible (v : Region Nat) :
    ¬ (SpineSolution FigureLabel (FigureGate false) (FigureContext false) v ∧ v 0) := by
  rintro ⟨h, observed⟩
  rw [(figure_and_off v).mp h] at observed
  exact observed

/-- Every full-carrier solution is exactly a source state and a spine solution. -/
theorem figure_full_fixed_iff (g b : Bool) (X : Region (LabelNode Unit)) :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate g)) (LabelContext (FigureContext b))) X ↔
    ∃ v, X = LabelState (FigureContext b) v ∧
      SpineSolution FigureLabel (FigureGate g) (FigureContext b) v := by
  constructor
  · intro fixed
    let v : Region Nat := fun n => X (.link n)
    have state := label_fixed_as_state FigureLabel (FigureGate g) (FigureContext b) X fixed
    refine ⟨v, state, ?_⟩
    apply (label_state_fixed_iff FigureLabel (FigureGate g) (FigureContext b) v).mp
    rw [← state]
    exact fixed
  · rintro ⟨v, rfl, sol⟩
    exact (label_state_fixed_iff FigureLabel (FigureGate g) (FigureContext b) v).mpr sol

theorem figure_full_and_off (X : Region (LabelNode Unit)) :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext false))) X ↔
    X = LabelState (FigureContext false) (fun _ => False) := by
  rw [figure_full_fixed_iff]
  simp only [figure_and_off]
  constructor
  · rintro ⟨v, h, rfl⟩
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem figure_full_or_on (X : Region (LabelNode Unit)) :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext true))) X ↔
    X = LabelState (FigureContext true) (fun _ => True) := by
  rw [figure_full_fixed_iff]
  simp only [figure_or_on]
  constructor
  · rintro ⟨v, h, rfl⟩
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem figure_full_and_on (X : Region (LabelNode Unit)) :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext true))) X ↔
    X = LabelState (FigureContext true) (fun _ => False) ∨
      X = LabelState (FigureContext true) (fun _ => True) := by
  rw [figure_full_fixed_iff]
  simp only [figure_and_on]
  constructor
  · rintro ⟨v, h, off | on⟩
    · subst v; exact Or.inl h
    · subst v; exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩

theorem figure_full_or_off (X : Region (LabelNode Unit)) :
    Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext false))) X ↔
    X = LabelState (FigureContext false) (fun _ => False) ∨
      X = LabelState (FigureContext false) (fun _ => True) := by
  rw [figure_full_fixed_iff]
  simp only [figure_or_off]
  constructor
  · rintro ⟨v, h, off | on⟩
    · subst v; exact Or.inl h
    · subst v; exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩

universe u

theorem all_roots_carrier_fixed {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (adm : Mechanism C D f) :
    Fixed (Step C D f (Roots C D)) C := by
  rw [all_roots_context_is_original adm]
  funext x
  apply propext
  constructor
  · intro h
    exact h.1
  · intro hx
    refine ⟨hx, ?_⟩
    have parents : (fun y => C y ∧ Parents C D x y) = Parents C D x := by
      funext y
      exact propext ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    change f x (fun y => C y ∧ Parents C D x y)
    rw [parents]
    exact (adm x hx).2.2

theorem all_roots_greatest_is_carrier {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (adm : Mechanism C D f) :
    Greatest (Step C D f (Roots C D)) = C := by
  apply funext
  intro x
  apply propext
  constructor
  · intro h
    exact contextual_fixed_carrier (fun _ h => h) (greatest_fixed (step_monotone adm _)) h
  · intro h
    exact (fixed_bounds (all_roots_carrier_fixed adm)).2 h

theorem all_roots_determined_is_least {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (adm : Mechanism C D f) :
    Determined C (Step C D f (Roots C D)) = Least (Step C D f (Roots C D)) := by
  funext x
  simp [Determined, all_roots_greatest_is_carrier adm]

def PairedSource (n : Nat) : Nat := n / 2

theorem constant_source_repeated : RepeatedInEveryTail FigureLabel := by
  intro N
  refine ⟨N, Nat.le_refl _, N+1, Nat.le_succ _, ?_, rfl⟩
  omega

theorem paired_source_repeated : RepeatedInEveryTail PairedSource := by
  intro N
  refine ⟨2*N, ?_, 2*N+1, ?_, ?_, ?_⟩
  all_goals (try simp only [PairedSource])
  all_goals omega

theorem paired_no_fixed_source_in_every_tail (b : Nat) :
    ∃ N, ∀ n, N ≤ n → PairedSource n ≠ b := by
  refine ⟨2*b+2, ?_⟩
  intro n hn h
  simp only [PairedSource] at h
  omega

theorem injective_sources_not_repeated {α : Type u} (l : Nat → α) (hinj : Function.Injective l) :
    ¬ RepeatedInEveryTail l := by
  intro h
  obtain ⟨i, _, j, _, neq, eq⟩ := h 0
  exact neq (hinj eq)

def UniformRelevantSynthesis {α : Type u} (l : Nat → α) : Prop :=
  ∃ f, Mechanism (fun _ => True) (LabelDependency l) f ∧
    Relevant (fun _ => True) (LabelDependency l) f ∧
    ContextDeterminate (fun _ => True) (LabelDependency l) f

theorem constant_source_uniform_synthesis : UniformRelevantSynthesis FigureLabel :=
  (relevant_labelled_spine_synthesis_iff FigureLabel).mpr constant_source_repeated

theorem paired_source_uniform_synthesis : UniformRelevantSynthesis PairedSource :=
  (relevant_labelled_spine_synthesis_iff PairedSource).mpr paired_source_repeated

theorem injective_sources_no_uniform_synthesis {α : Type u} (l : Nat → α)
    (hinj : Function.Injective l) : ¬ UniformRelevantSynthesis l := by
  intro h
  exact injective_sources_not_repeated l hinj ((relevant_labelled_spine_synthesis_iff l).mp h)

/-- AND is pointwise below OR, including inputs not constrained by a solution. -/
theorem figure_and_pointwise_le_or (x : LabelNode Unit) (S : Region (LabelNode Unit)) :
    LabelGateMechanism FigureLabel (FigureGate false) x S →
      LabelGateMechanism FigureLabel (FigureGate true) x S := by
  cases x with
  | root b => simp [LabelGateMechanism]
  | link n =>
    change (S (.root (FigureLabel n)) ∧ S (.link (n+1))) →
      (S (.root (FigureLabel n)) ∨ S (.link (n+1)))
    exact fun h => Or.inl h.1

theorem figure_and_off_link_determined (n : Nat) :
    Determined (fun _ => True)
      (Step (fun _ => True) (LabelDependency FigureLabel)
        (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext false))) (.link n) := by
  apply (determined_iff_fixed_agreement (label_gate_admissible FigureLabel (FigureGate false))
    (label_context_legal FigureLabel (FigureContext false)) True.intro).mpr
  intro X Y fx fy
  rw [(figure_full_and_off X).mp fx, (figure_full_and_off Y).mp fy]

theorem figure_or_off_link_ambiguous (n : Nat) :
    ¬ Determined (fun _ => True)
      (Step (fun _ => True) (LabelDependency FigureLabel)
        (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext false))) (.link n) := by
  intro det
  have agree := (determined_iff_fixed_agreement (label_gate_admissible FigureLabel (FigureGate true))
    (label_context_legal FigureLabel (FigureContext false)) True.intro).mp det
  have eq := agree (LabelState (FigureContext false) (fun _ => False))
    (LabelState (FigureContext false) (fun _ => True))
    ((figure_full_or_off _).mpr (Or.inl rfl)) ((figure_full_or_off _).mpr (Or.inr rfl))
  exact eq.mpr True.intro

/-- A formal input witness; it is not asserted to be a globally compatible solution. -/
theorem majority_successor_sensitive (n : Nat) :
    let S : Region CopyNode := fun x => x = .root n
    Sub S (fun z => Parents (fun _ => True) CopyDependency (.link n) z ∧ z ≠ .link (n+1)) ∧
      ¬ CopyMechanism (.link n) S ∧
      CopyMechanism (.link n) (fun z => z = .link (n+1) ∨ S z) := by
  dsimp
  constructor
  · intro z hz
    subst z
    simp [Parents, CopyDependency]
  · simp [CopyMechanism, Majority]

theorem figure_full_and_off_observation_impossible (X : Region (LabelNode Unit)) (n : Nat) :
    ¬ (Fixed (Step (fun _ => True) (LabelDependency FigureLabel)
      (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext false))) X ∧
      X (.link n)) := by
  rintro ⟨fixed, observed⟩
  rw [(figure_full_and_off X).mp fixed] at observed
  exact observed

theorem figure_link_states_distinct (b : Bool) :
    LabelState (FigureContext b) (fun _ => False) ≠ LabelState (FigureContext b) (fun _ => True) := by
  intro eq
  have h := congrFun eq (.link 0)
  exact Eq.mpr h True.intro

theorem figure_determined_not_pointwise_monotone :
    ¬ Sub
      (Determined (fun _ => True) (Step (fun _ => True) (LabelDependency FigureLabel)
        (LabelGateMechanism FigureLabel (FigureGate false)) (LabelContext (FigureContext false))))
      (Determined (fun _ => True) (Step (fun _ => True) (LabelDependency FigureLabel)
        (LabelGateMechanism FigureLabel (FigureGate true)) (LabelContext (FigureContext false)))) := by
  intro h
  exact figure_or_off_link_ambiguous 0 (h (figure_and_off_link_determined 0))

/-- These opposite source/copy settings are formal parent inputs; they need not be solutions. -/
def MajorityOppositeInput (b : Bool) (n : Nat) : Region CopyNode :=
  if b then (fun x => x = .root n) else (fun x => x = .copy n)

theorem majority_sensitive_at_fixed_source (b : Bool) (n : Nat) :
    let S := MajorityOppositeInput b n
    (S (.root n) ↔ b = true) ∧ (S (.copy n) ↔ b = false) ∧
      Sub S (fun z => Parents (fun _ => True) CopyDependency (.link n) z ∧ z ≠ .link (n+1)) ∧
      ¬ CopyMechanism (.link n) S ∧
      CopyMechanism (.link n) (fun z => z = .link (n+1) ∨ S z) := by
  cases b <;> simp [MajorityOppositeInput, Sub, Parents, CopyDependency, CopyMechanism, Majority]

theorem labelled_spine_all_root_reachable {α : Type u} (l : Nat → α) :
    Sub (fun _ => True) (RootReachable (fun _ => True) (LabelDependency l)) := by
  intro x _
  cases x with
  | root b =>
    refine ⟨.root b, ⟨True.intro, ?_⟩, InternalPath.refl _ True.intro⟩
    intro y h
    exact h.2
  | link n =>
    refine ⟨.root (l n), ⟨True.intro, ?_⟩, ?_⟩
    · intro y h
      exact h.2
    · exact InternalPath.step (InternalPath.refl _ True.intro) True.intro (Or.inl rfl)

theorem labelled_spine_contextwise_synthesis {α : Type u} (l : Nat → α)
    (U : Region (LabelNode α)) (ctx : Sub U (Roots (fun _ => True) (LabelDependency l))) :
    ∃ f, Mechanism (fun _ => True) (LabelDependency l) f ∧
      Relevant (fun _ => True) (LabelDependency l) f ∧
      UniqueFixed (Step (fun _ => True) (LabelDependency l) f U) := by
  apply (some_relevant_context_unique_iff_local_foundation ctx).mpr
  exact (local_foundation_iff_all_reachable _ _).mpr (labelled_spine_all_root_reachable l)

theorem injective_sources_quantifier_separation {α : Type u} (l : Nat → α)
    (hinj : Function.Injective l) :
    (∀ U, Sub U (Roots (fun _ => True) (LabelDependency l)) →
      ∃ f, Mechanism (fun _ => True) (LabelDependency l) f ∧
        Relevant (fun _ => True) (LabelDependency l) f ∧
        UniqueFixed (Step (fun _ => True) (LabelDependency l) f U)) ∧
      ¬ UniformRelevantSynthesis l := by
  exact ⟨labelled_spine_contextwise_synthesis l, injective_sources_no_uniform_synthesis l hinj⟩

end DeterminationPatterns
