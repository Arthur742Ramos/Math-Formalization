module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for shared-spine region classification. -/
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

/-- Finite dependency paths whose vertices all lie in the given region. -/
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


/-- K lies in C, contains the roots, has internal root paths, and contains each
carrier vertex whose every carrier parent lies in K. -/
def RegionConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (K : Region α) : Prop :=
  Sub K C ∧ Sub (Roots C D) K ∧ InternalReach K D (Roots C D) = K ∧
  (∀ x, C x → (∀ y, Parents C D x y → K y) → K x)


theorem exists_min_nat (P : Nat → Prop) (existsP : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  classical
  obtain ⟨n, hn⟩ := existsP
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hm⟩ := smaller
      exact ih m hmn hm
    · exact ⟨n, hn, fun m hmn hm => smaller ⟨m, hmn, hm⟩⟩


/-- A source and countably many numbered links. -/
inductive SpineNode where
  | source : SpineNode
  | link : Nat → SpineNode
  deriving DecidableEq

/-- The source and link n+1 are parents of link n; the source has no parent. -/
def SpineDependency (y x : SpineNode) : Prop :=
  match x with
  | .source => False
  | .link n => y = .source ∨ y = .link (n+1)

/-- The source together with links below N; N=0 gives the source alone. -/
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

/-- The graph region criterion is source inclusion and downward closure. -/
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

/-- Source inclusion and downward closure classify full and finite-prefix regions. -/
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


end DeterminationPatterns
