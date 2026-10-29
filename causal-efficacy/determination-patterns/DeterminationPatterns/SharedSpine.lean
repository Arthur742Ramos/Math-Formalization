module
public import DeterminationPatterns.Uniform
@[expose] public section
namespace DeterminationPatterns
universe u

inductive SpineNode where
  | source : SpineNode
  | link : Nat → SpineNode
  deriving DecidableEq

def SpineDependency (y x : SpineNode) : Prop :=
  match x with
  | .source => False
  | .link n => y = .source ∨ y = .link (n+1)

def SpinePrefix (N : Nat) : Region SpineNode := fun x =>
  match x with
  | .source => True
  | .link n => n < N

theorem spine_source_root : Roots (fun _ => True) SpineDependency .source := by
  simp [Roots, Parents, SpineDependency]

theorem spine_roots_exact (x : SpineNode) :
    Roots (fun _ => True) SpineDependency x ↔ x = .source := by
  cases x with
  | source => simp [spine_source_root]
  | link n =>
    constructor
    · intro hr; exact False.elim (hr.2 .source ⟨True.intro, Or.inl rfl⟩)
    · intro bad; cases bad

theorem shared_spine_region_conditions (K : Region SpineNode) :
    RegionConditions (fun _ => True) SpineDependency K ↔
      K .source ∧ ∀ n, K (.link (n+1)) → K (.link n) := by
  constructor
  · intro reg
    refine ⟨reg.2.1 spine_source_root, ?_⟩
    intro n hn
    apply reg.2.2.2 (.link n) True.intro
    intro y hy
    rcases hy.2 with hy | hy
    · rw [hy]; exact reg.2.1 spine_source_root
    · rw [hy]; exact hn
  · rintro ⟨src, down⟩
    have rootsK : Sub (Roots (fun _ => True) SpineDependency) K := by
      intro x hr
      rw [(spine_roots_exact x).mp hr]
      exact src
    have reach : InternalReach K SpineDependency (Roots (fun _ => True) SpineDependency) = K := by
      funext x
      apply propext
      constructor
      · intro ⟨_, _, hp⟩; exact path_target hp
      · intro hx
        cases x with
        | source => exact ⟨SpineNode.source, spine_source_root, InternalPath.refl SpineNode.source src⟩
        | link n =>
          exact ⟨SpineNode.source, spine_source_root,
            InternalPath.step (InternalPath.refl SpineNode.source src) hx (Or.inl rfl)⟩
    have closed : ∀ x, True → (∀ y, Parents (fun _ => True) SpineDependency x y → K y) → K x := by
      intro x _ allp
      cases x with
      | source => exact src
      | link n => exact down n (allp (.link (n+1)) ⟨True.intro, Or.inr rfl⟩)
    exact ⟨(fun _ _ => True.intro), rootsK, reach, closed⟩

theorem spine_downward (K : Region SpineNode)
    (down : ∀ n, K (.link (n+1)) → K (.link n)) {m n : Nat} (h : m ≤ n) :
    K (.link n) → K (.link m) := by
  induction h with
  | refl => intro hx; exact hx
  | @step n h ih =>
    intro hx
    exact ih (down n hx)

theorem shared_spine_initial_segments (K : Region SpineNode) :
    (K .source ∧ ∀ n, K (.link (n+1)) → K (.link n)) ↔
      K = (fun _ => True) ∨ ∃ N, K = SpinePrefix N := by
  classical
  constructor
  · rintro ⟨src, down⟩
    by_cases all : ∀ n, K (.link n)
    · left
      funext x
      apply propext
      cases x with
      | source => exact ⟨fun _ => True.intro, fun _ => src⟩
      | link n => exact ⟨fun _ => True.intro, fun _ => all n⟩
    · right
      have missing : ∃ n, ¬ K (.link n) := by
        apply Classical.byContradiction
        intro h
        apply all
        intro n
        apply Classical.byContradiction
        intro hn
        exact h ⟨n, hn⟩
      obtain ⟨N, notN, minimal⟩ := exists_min_nat (fun n => ¬ K (.link n)) missing
      refine ⟨N, ?_⟩
      funext x
      apply propext
      cases x with
      | source => exact ⟨fun _ => True.intro, fun _ => src⟩
      | link n =>
        change K (.link n) ↔ n < N
        constructor
        · intro hn
          apply Classical.byContradiction
          intro hnot
          have hle : N ≤ n := Nat.le_of_not_gt hnot
          exact notN (spine_downward K down hle hn)
        · intro hlt
          apply Classical.byContradiction
          intro hnot
          exact minimal n hlt hnot
  · intro h
    rcases h with hall | ⟨N, hprefix⟩
    · rw [hall]; exact ⟨True.intro, fun _ _ => True.intro⟩
    · rw [hprefix]
      refine ⟨True.intro, ?_⟩
      intro n hn
      exact Nat.lt_of_succ_lt hn

theorem shared_spine_attainable_initial_segments (K U : Region SpineNode)
    (ctx : Sub U (fun x => x = .source)) :
    (∃ f, Mechanism (fun _ => True) SpineDependency f ∧ Relevant (fun _ => True) SpineDependency f ∧
      Determined (fun _ => True) (Step (fun _ => True) SpineDependency f U) = K) ↔
      K = (fun _ => True) ∨ ∃ N, K = SpinePrefix N := by
  have legal : Sub U (Roots (fun _ => True) SpineDependency) := by
    intro x hx
    rw [ctx hx]
    exact spine_source_root
  exact (exact_relevant_region_realization legal).trans
    ((shared_spine_region_conditions K).trans (shared_spine_initial_segments K))

end DeterminationPatterns
