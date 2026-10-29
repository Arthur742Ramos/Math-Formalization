module
public import DeterminationPatterns.PaperGrounded
@[expose] public section

/-! Possible-input graph facts for the paper's source-labelled spines. -/
namespace DeterminationPatterns
universe u

theorem labelled_root_has_no_parents {α : Type u} (l : Nat → α) (b : α) :
    Parents (fun _ => True) (LabelDependency l) (.root b) = (fun _ => False) := by
  funext y
  apply propext
  simp [Parents, LabelDependency]

theorem labelled_link_parents_exact {α : Type u} (l : Nat → α) (n : Nat) :
    Parents (fun _ => True) (LabelDependency l) (.link n) =
      (fun y => y = .root (l n) ∨ y = .link (n+1)) := by
  funext y
  apply propext
  simp [Parents, LabelDependency]

theorem labelled_link_two_parents_distinct {α : Type u} (l : Nat → α) (n : Nat) :
    LabelNode.root (l n) ≠ LabelNode.link (n+1) := by
  intro h
  cases h

theorem labelled_roots_exact {α : Type u} (l : Nat → α) (x : LabelNode α) :
    Roots (fun _ => True) (LabelDependency l) x ↔ ∃ b, x = .root b := by
  cases x with
  | root b => simp [Roots, Parents, LabelDependency]
  | link n =>
    constructor
    · intro h
      exact False.elim (h.2 (.root (l n)) ⟨True.intro, Or.inl rfl⟩)
    · rintro ⟨b, h⟩
      cases h

theorem labelled_link_root_distance_one {α : Type u} (l : Nat → α) (n : Nat) :
    RootLength (fun _ => True) (LabelDependency l) 1 (.link n) ∧
      ¬ RootLength (fun _ => True) (LabelDependency l) 0 (.link n) := by
  constructor
  · have root : Roots (fun _ => True) (LabelDependency l) (.root (l n)) :=
      (labelled_roots_exact l _).mpr ⟨_, rfl⟩
    exact RootLength.step (RootLength.root _ root) True.intro (Or.inl rfl)
  · intro h
    cases h with
    | root _ hroot =>
      exact (hroot.2 (.root (l n)) ⟨True.intro, Or.inl rfl⟩)

theorem labelled_path_from_link {α : Type u} (l : Nat → α) {n : Nat} {x : LabelNode α}
    (path : InternalPath (fun _ => True) (LabelDependency l) (.link n) x) :
    ∃ m, x = .link m ∧ m ≤ n := by
  induction path with
  | refl => exact ⟨n, rfl, Nat.le_refl n⟩
  | @step y x path hx edge ih =>
    obtain ⟨m, rfl, hm⟩ := ih
    cases x with
    | root c => exact False.elim edge
    | link k =>
      change LabelNode.link m = .root (l k) ∨ LabelNode.link m = .link (k+1) at edge
      rcases edge with impossible | eq
      · cases impossible
      · have e : m = k+1 := LabelNode.link.inj eq
        exact ⟨k, rfl, by omega⟩

theorem labelled_graph_acyclic {α : Type u} (l : Nat → α) :
    ∀ x y, LabelDependency l x y →
      ¬ InternalPath (fun _ => True) (LabelDependency l) y x := by
  intro x y edge path
  cases y with
  | root b => exact edge
  | link n =>
    cases x with
    | root b =>
      obtain ⟨m, h, _⟩ := labelled_path_from_link l path
      cases h
    | link m =>
      have shape : LabelNode.link m = .root (l n) ∨ LabelNode.link m = .link (n+1) := edge
      rcases shape with impossible | eq
      · cases impossible
      · have e : m = n+1 := LabelNode.link.inj eq
        obtain ⟨k, same, bound⟩ := labelled_path_from_link l path
        have keq : m = k := LabelNode.link.inj same
        omega

theorem labelled_link_not_accessible {α : Type u} (l : Nat → α) (n : Nat) :
    ¬ Acc (RestrictedEdge (fun _ => True) (LabelDependency l)) (.link n) := by
  have no : ∀ x, Acc (RestrictedEdge (fun _ => True) (LabelDependency l)) x →
      ∀ n, x = .link n → False := by
    intro x acc
    induction acc with
    | intro x prev ih =>
      intro n eq
      subst x
      exact ih (.link (n+1)) ⟨True.intro, True.intro, Or.inr rfl⟩ (n+1) rfl
  exact fun h => no _ h n rfl

theorem labelled_graph_not_well_founded {α : Type u} (l : Nat → α) :
    ¬ WellFounded (RestrictedEdge (fun _ => True) (LabelDependency l)) := by
  intro wf
  exact labelled_link_not_accessible l 0 (wf.apply (.link 0))

theorem figure_source_infinite_successors :
    Function.Injective (fun n : Nat => LabelNode.link n : Nat → LabelNode Unit) ∧
      ∀ n, LabelDependency FigureLabel (.root ()) (.link n) := by
  constructor
  · intro m n h
    exact LabelNode.link.inj h
  · intro n
    exact Or.inl rfl

/-- Sensitivity here compares the successor input at fixed source value. -/
def GateSuccessorSensitive (g b : Bool) : Prop :=
  ¬ SpineGate g b False ∧ SpineGate g b True

theorem gate_successor_sensitive_iff (g b : Bool) :
    GateSuccessorSensitive g b ↔ g ≠ b := by
  cases g <;> cases b <;> simp [GateSuccessorSensitive, SpineGate]

def SensitiveSuccessor {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (y x : Nat) : Prop :=
  y = x+1 ∧ GateSuccessorSensitive (g x) (u (l x))

theorem cofinal_forcing_sensitive_well_founded {α : Type u} (l : Nat → α)
    (g : Nat → Bool) (u : α → Bool) (force : CofinalForcing l g u) :
    WellFounded (SensitiveSuccessor l g u) := by
  have bounded : ∀ k n, (∃ m, n ≤ m ∧ m ≤ n+k ∧ g m = u (l m)) →
      Acc (SensitiveSuccessor l g u) n := by
    intro k
    induction k with
    | zero =>
      intro n ⟨m, lo, hi, forced⟩
      have eq : m = n := by omega
      subst m
      apply Acc.intro n
      intro y edge
      exact False.elim (((gate_successor_sensitive_iff _ _).mp edge.2) forced)
    | succ k ih =>
      intro n ⟨m, lo, hi, forced⟩
      by_cases atN : g n = u (l n)
      · apply Acc.intro n
        intro y edge
        exact False.elim (((gate_successor_sensitive_iff _ _).mp edge.2) atN)
      · have neq : m ≠ n := by
          intro eq
          subst m
          exact atN forced
        apply Acc.intro n
        intro y edge
        have eq : y = n+1 := edge.1
        subst y
        apply ih (n+1)
        exact ⟨m, by omega, by omega, forced⟩
  constructor
  intro n
  obtain ⟨m, hn, forced⟩ := force n
  apply bounded (m-n) n
  exact ⟨m, hn, by omega, forced⟩

end DeterminationPatterns
