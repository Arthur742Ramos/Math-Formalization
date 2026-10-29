module
public import DeterminationPatterns.PaperGrounded
@[expose] public section

/-! The finite-parent stage-ω observation for the universal-parent operator.
No finite carrier or finite-stage stabilization is assumed. -/
namespace DeterminationPatterns
universe u

def FoundationStep {α : Type u} (C : Region α) (D : α → α → Prop)
    (X : Region α) : Region α :=
  fun x => C x ∧ ∀ y, Parents C D x y → X y

def FiniteParentCover {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → ∃ ps : List α, ∀ y, Parents C D x y → y ∈ ps

def CountableUnion {α : Type u} (X : Nat → Region α) : Region α :=
  fun x => ∃ n, X n x

theorem increasing_sequence_le {α : Type u} (X : Nat → Region α)
    (inc : ∀ n, Sub (X n) (X (n+1))) {n m : Nat} (h : n ≤ m) : Sub (X n) (X m) := by
  induction h with
  | refl => intro x hx; exact hx
  | @step m h ih => intro x hx; exact inc m (ih hx)

theorem finite_cover_common_stage {α : Type u} (ps : List α) (P : Region α)
    (X : Nat → Region α) (inc : ∀ n, Sub (X n) (X (n+1)))
    (available : ∀ y, P y → ∃ n, X n y) :
    ∃ n, ∀ y, y ∈ ps → P y → X n y := by
  classical
  induction ps with
  | nil => exact ⟨0, by simp⟩
  | cons a ps ih =>
    obtain ⟨n, hn⟩ := ih
    by_cases ha : P a
    · obtain ⟨m, hm⟩ := available a ha
      refine ⟨max n m, ?_⟩
      intro y hy hp
      rcases List.mem_cons.mp hy with eq | member
      · subst y
        exact increasing_sequence_le X inc (Nat.le_max_right n m) hm
      · exact increasing_sequence_le X inc (Nat.le_max_left n m) (hn y member hp)
    · refine ⟨n, ?_⟩
      intro y hy hp
      rcases List.mem_cons.mp hy with eq | member
      · subst y
        exact False.elim (ha hp)
      · exact hn y member hp

theorem foundation_step_monotone {α : Type u} (C : Region α) (D : α → α → Prop) :
    Monotone (FoundationStep C D) := by
  intro A B sub x h
  exact ⟨h.1, fun y hy => sub (h.2 y hy)⟩

theorem foundation_preserves_increasing_union {α : Type u} {C : Region α}
    {D : α → α → Prop} (finite : FiniteParentCover C D) (X : Nat → Region α)
    (inc : ∀ n, Sub (X n) (X (n+1))) :
    FoundationStep C D (CountableUnion X) = CountableUnion (fun n => FoundationStep C D (X n)) := by
  funext x
  apply propext
  constructor
  · rintro ⟨hc, all⟩
    obtain ⟨ps, covers⟩ := finite x hc
    obtain ⟨n, hn⟩ := finite_cover_common_stage ps (Parents C D x) X inc all
    exact ⟨n, hc, fun y hy => hn y (covers y hy) hy⟩
  · rintro ⟨n, hc, all⟩
    exact ⟨hc, fun y hy => ⟨n, all y hy⟩⟩

def FoundationStage {α : Type u} (C : Region α) (D : α → α → Prop) : Nat → Region α
  | 0 => fun _ => False
  | n+1 => FoundationStep C D (FoundationStage C D n)

def FoundationOmega {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  CountableUnion (FoundationStage C D)

theorem foundation_stage_increasing {α : Type u} (C : Region α) (D : α → α → Prop) :
    ∀ n, Sub (FoundationStage C D n) (FoundationStage C D (n+1)) := by
  intro n
  induction n with
  | zero => intro x h; exact False.elim h
  | succ n ih => exact foundation_step_monotone C D _ _ ih

theorem foundation_omega_fixed {α : Type u} {C : Region α} {D : α → α → Prop}
    (finite : FiniteParentCover C D) : Fixed (FoundationStep C D) (FoundationOmega C D) := by
  have continuity := foundation_preserves_increasing_union finite (FoundationStage C D)
    (foundation_stage_increasing C D)
  funext x
  apply propext
  constructor
  · intro h
    have hunion := (Iff.of_eq (congrFun continuity x)).mp h
    obtain ⟨n, hn⟩ := hunion
    exact ⟨n+1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact False.elim hn
    | succ n => exact (Iff.of_eq (congrFun continuity x)).mpr ⟨n, hn⟩

theorem foundation_omega_least {α : Type u} {C : Region α} {D : α → α → Prop}
    (finite : FiniteParentCover C D) : FoundationOmega C D = Least (FoundationStep C D) := by
  have stages : ∀ n, Sub (FoundationStage C D n) (Least (FoundationStep C D)) := by
    intro n
    induction n with
    | zero => intro x h; exact False.elim h
    | succ n ih =>
      intro x hx
      have next := foundation_step_monotone C D _ _ ih hx
      rw [least_fixed (foundation_step_monotone C D)] at next
      exact next
  funext x
  apply propext
  constructor
  · rintro ⟨n, hn⟩
    exact stages n hn
  · intro h
    exact (fixed_bounds (foundation_omega_fixed finite)).1 h

theorem foundation_least_accessible {α : Type u} (C : Region α) (D : α → α → Prop) :
    Least (FoundationStep C D) = AccessibleRegion C D := by
  have pre : Sub (FoundationStep C D (AccessibleRegion C D)) (AccessibleRegion C D) := by
    intro x ⟨hc, all⟩
    refine ⟨hc, Acc.intro x ?_⟩
    intro y edge
    exact (all y ⟨edge.1, edge.2.2⟩).2
  have down : Sub (AccessibleRegion C D) (Least (FoundationStep C D)) := by
    intro x ⟨hc, acc⟩
    induction acc with
    | intro x prev ih =>
      have step : FoundationStep C D (Least (FoundationStep C D)) x := by
        refine ⟨hc, ?_⟩
        intro y hy
        exact ih y ⟨hy.1, hc, hy.2⟩ hy.1
      rw [least_fixed (foundation_step_monotone C D)] at step
      exact step
  funext x
  exact propext ⟨fun h => least_le _ _ pre h, fun h => down h⟩

theorem finite_parents_omega_accessibility {α : Type u} {C : Region α}
    {D : α → α → Prop} (finite : FiniteParentCover C D) :
    FoundationOmega C D = AccessibleRegion C D :=
  (foundation_omega_least finite).trans (foundation_least_accessible C D)

/-- Finite parent sets also give continuity for any admissible contextual mechanism. -/
theorem contextual_step_preserves_increasing_union {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} (adm : Mechanism C D f)
    (finite : FiniteParentCover C D) (U : Region α) (X : Nat → Region α)
    (inc : ∀ n, Sub (X n) (X (n+1))) :
    Step C D f U (CountableUnion X) = CountableUnion (fun n => Step C D f U (X n)) := by
  funext x
  apply propext
  constructor
  · intro h
    rcases h with hu | ⟨hc, hp, hf⟩
    · exact ⟨0, Or.inl hu⟩
    · obtain ⟨ps, covers⟩ := finite x hc
      let P : Region α := fun y => CountableUnion X y ∧ Parents C D x y
      have available : ∀ y, P y → ∃ n, X n y := by intro y hy; exact hy.1
      obtain ⟨n, hn⟩ := finite_cover_common_stage ps P X inc available
      have eq : (fun y => CountableUnion X y ∧ Parents C D x y) =
          (fun y => X n y ∧ Parents C D x y) := by
        funext y
        apply propext
        constructor
        · intro hy
          exact ⟨hn y (covers y hy.2) hy, hy.2⟩
        · intro hy
          exact ⟨⟨n, hy.1⟩, hy.2⟩
      rw [eq] at hf
      exact ⟨n, Or.inr ⟨hc, hp, hf⟩⟩
  · rintro ⟨n, hn⟩
    have sub : Sub (X n) (CountableUnion X) := by intro y hy; exact ⟨n, hy⟩
    exact step_monotone adm U _ _ sub hn

def ContextStage {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U : Region α) : Nat → Region α
  | 0 => fun _ => False
  | n+1 => Step C D f U (ContextStage C D f U n)

def ContextOmega {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U : Region α) : Region α :=
  CountableUnion (ContextStage C D f U)

theorem context_stage_increasing {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (adm : Mechanism C D f) (U : Region α) :
    ∀ n, Sub (ContextStage C D f U n) (ContextStage C D f U (n+1)) := by
  intro n
  induction n with
  | zero => intro x h; exact False.elim h
  | succ n ih => exact step_monotone adm U _ _ ih

theorem finite_parents_context_omega_least {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} (adm : Mechanism C D f)
    (finite : FiniteParentCover C D) (U : Region α) :
    ContextOmega C D f U = Least (Step C D f U) := by
  let F := Step C D f U
  have continuity := contextual_step_preserves_increasing_union adm finite U
    (ContextStage C D f U) (context_stage_increasing adm U)
  have fixed : Fixed F (ContextOmega C D f U) := by
    funext x
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := (Iff.of_eq (congrFun continuity x)).mp h
      exact ⟨n+1, hn⟩
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact False.elim hn
      | succ n => exact (Iff.of_eq (congrFun continuity x)).mpr ⟨n, hn⟩
  have stages : ∀ n, Sub (ContextStage C D f U n) (Least F) := by
    intro n
    induction n with
    | zero => intro x h; exact False.elim h
    | succ n ih =>
      intro x hx
      have next := step_monotone adm U _ _ ih hx
      rw [least_fixed (step_monotone adm U)] at next
      exact next
  funext x
  apply propext
  constructor
  · rintro ⟨n, hn⟩
    exact stages n hn
  · intro h
    exact (fixed_bounds fixed).1 h

/-- A chain of finite-depth nodes and one node depending on every chain node. -/
def DepthDependency (y x : Option Nat) : Prop :=
  match x with
  | none => ∃ n, y = some n
  | some 0 => False
  | some (n+1) => y = some n

theorem depth_stage_some_iff (k n : Nat) :
    FoundationStage (fun _ : Option Nat => True) DepthDependency k (some n) ↔ n < k := by
  induction k generalizing n with
  | zero => simp [FoundationStage]
  | succ k ih =>
    cases n with
    | zero => simp [FoundationStage, FoundationStep, Parents, DepthDependency]
    | succ n =>
      constructor
      · rintro ⟨_, all⟩
        have previous := all (some n) ⟨True.intro, rfl⟩
        have depth := (ih n).mp previous
        omega
      · intro h
        refine ⟨True.intro, ?_⟩
        intro y hy
        have eq : y = some n := hy.2
        subst y
        exact (ih n).mpr (by omega)

theorem depth_limit_not_in_omega :
    ¬ FoundationOmega (fun _ : Option Nat => True) DepthDependency none := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact hk
  | succ k =>
    have previous := hk.2 (some k) ⟨True.intro, ⟨k, rfl⟩⟩
    have impossible := (depth_stage_some_iff k k).mp previous
    omega

theorem depth_limit_enters_after_omega :
    FoundationStep (fun _ : Option Nat => True) DepthDependency
      (FoundationOmega (fun _ : Option Nat => True) DepthDependency) none := by
  refine ⟨True.intro, ?_⟩
  rintro y ⟨_, n, rfl⟩
  exact ⟨n+1, (depth_stage_some_iff (n+1) n).mpr (Nat.lt_succ_self n)⟩

theorem depth_limit_accessible :
    AccessibleRegion (fun _ : Option Nat => True) DepthDependency none := by
  let C : Region (Option Nat) := fun _ => True
  let F := FoundationStep C DepthDependency
  have stages : ∀ k, Sub (FoundationStage C DepthDependency k) (Least F) := by
    intro k
    induction k with
    | zero => intro x h; exact False.elim h
    | succ k ih =>
      intro x hx
      have next := foundation_step_monotone C DepthDependency _ _ ih hx
      rw [least_fixed (foundation_step_monotone C DepthDependency)] at next
      exact next
  have step : F (Least F) none := by
    refine ⟨True.intro, ?_⟩
    rintro y ⟨_, n, rfl⟩
    exact stages (n+1) ((depth_stage_some_iff (n+1) n).mpr (Nat.lt_succ_self n))
  change FoundationStep C DepthDependency (Least (FoundationStep C DepthDependency)) none at step
  rw [least_fixed (foundation_step_monotone C DepthDependency)] at step
  rw [← foundation_least_accessible C DepthDependency]
  exact step

theorem depth_limit_strictly_after_omega :
    AccessibleRegion (fun _ : Option Nat => True) DepthDependency none ∧
      ¬ FoundationOmega (fun _ : Option Nat => True) DepthDependency none ∧
      FoundationStep (fun _ : Option Nat => True) DepthDependency
        (FoundationOmega (fun _ : Option Nat => True) DepthDependency) none :=
  ⟨depth_limit_accessible, depth_limit_not_in_omega, depth_limit_enters_after_omega⟩

theorem labelled_spine_finite_parents {α : Type u} (l : Nat → α) :
    FiniteParentCover (fun _ => True) (LabelDependency l) := by
  intro x _
  cases x with
  | root b =>
    refine ⟨[], ?_⟩
    intro y hy
    exact False.elim hy.2
  | link n =>
    refine ⟨[.root (l n), .link (n+1)], ?_⟩
    intro y hy
    simpa [Parents, LabelDependency] using hy

theorem depth_has_infinite_parent_set :
    ¬ FiniteParentCover (fun _ : Option Nat => True) DepthDependency := by
  intro finite
  have fixed := foundation_omega_fixed finite
  have next := depth_limit_enters_after_omega
  rw [fixed] at next
  exact depth_limit_not_in_omega next

end DeterminationPatterns
