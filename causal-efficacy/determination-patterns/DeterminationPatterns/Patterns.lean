module
public import DeterminationPatterns.Bridges
@[expose] public section

namespace DeterminationPatterns
universe u

/-- A finite path whose vertices all belong to A, including its endpoints. -/
inductive InternalPath {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop where
  | refl (x : α) : A x → InternalPath A D x x
  | step {b y x : α} : InternalPath A D b y → A x → D y x → InternalPath A D b x

/-- Reachability along finite, carrier-internal paths from B. -/
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
  have rl : Sub R L := by
    intro x h
    rcases h with ⟨b, hb, hp⟩
    exact path_target hp
  have ul : Sub U L := by
    intro x hu
    have hf : F L x := Or.inl hu
    rw [lf] at hf
    exact hf
  have pre : Sub (F R) R := by
    intro x hx
    have hxl : L x := by
      have : F L x := lm R L rl hx
      rw [lf] at this
      exact this
    rcases hx with hu | ⟨hc, ⟨p, hp⟩, hf⟩
    · exact ⟨x, hu, InternalPath.refl x hxl⟩
    · have parent : ∃ y, R y ∧ Parents C D x y := by
        apply Classical.byContradiction
        intro hn
        have eq : (fun y => R y ∧ Parents C D x y) = (fun _ => False) := by
          funext y
          apply propext
          constructor
          · intro hy; exact hn ⟨y, hy⟩
          · intro hy; exact False.elim hy
        have hf0 : f x (fun _ => False) := by rw [← eq]; exact hf
        have noParents := (adm x hc).2.1.mp hf0
        exact noParents p hp
      obtain ⟨y, ⟨b, hb, path⟩, hyP⟩ := parent
      exact ⟨b, hb, InternalPath.step path hxl hyP.2⟩
  apply funext
  intro x
  exact propext ⟨fun hx => rl hx, fun hx => least_le F R pre hx⟩

theorem active_determinate_is_least {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} {U X : Region α} {a : α}
    (_adm : Mechanism C D f) (_ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) (active : X a)
    (det : Determined C (Step C D f U) a) : Least (Step C D f U) a := by
  rcases det with hl | ⟨_, hnot⟩
  · exact hl
  · exact False.elim (hnot ((fixed_bounds fixed).2 active))

/-- An active, determinate vertex in a solution has an internal path from an
active root, wholly within the least solution. -/
theorem active_determinate_internal_root_path {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} {U X : Region α} {a : α}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D))
    (fixed : Fixed (Step C D f U) X) (active : X a)
    (det : Determined C (Step C D f U) a) :
    InternalReach (Least (Step C D f U)) D U a := by
  rw [contextual_least_internal_paths adm ctx]
  exact active_determinate_is_least adm ctx fixed active det

/-- Reflexive transitive closure, independently phrased with a restricted edge. -/
inductive FiniteClosure {α : Type u} (r : α → α → Prop) : α → α → Prop where
  | refl (x : α) : FiniteClosure r x x
  | step {b y x : α} : FiniteClosure r b y → r y x → FiniteClosure r b x

def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x

theorem internal_path_to_closure {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (path : InternalPath A D b x) : FiniteClosure (RestrictedEdge A D) b x := by
  induction path with
  | refl hx => exact FiniteClosure.refl _
  | step path hx edge ih =>
    exact FiniteClosure.step ih ⟨path_target path, hx, edge⟩

theorem closure_to_internal_path {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (path : FiniteClosure (RestrictedEdge A D) b x) :
    A x → InternalPath A D b x := by
  induction path with
  | refl => intro hx; exact InternalPath.refl _ hx
  | step path edge ih =>
    intro hx
    exact InternalPath.step (ih edge.1) hx edge.2.2

theorem internal_reach_source_form {α : Type u} (A : Region α) (D : α → α → Prop)
    (B : Region α) (x : α) :
    InternalReach A D B x ↔ A x ∧ ∃ b, B b ∧ FiniteClosure (RestrictedEdge A D) b x := by
  constructor
  · rintro ⟨b, hb, hp⟩
    exact ⟨path_target hp, b, hb, internal_path_to_closure hp⟩
  · rintro ⟨hx, b, hb, hp⟩
    exact ⟨b, hb, closure_to_internal_path hp hx⟩

end DeterminationPatterns
