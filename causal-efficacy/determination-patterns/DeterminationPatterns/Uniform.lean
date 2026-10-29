module
public import DeterminationPatterns.CopyMajority
@[expose] public section
namespace DeterminationPatterns
universe u

/-- The source's local foundation for the entire carrier: every grounded
member has an independent ancestor within the carrier. -/
def LocalFoundation {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → (∃ y, Parents C D x y) → RootReachable C D x

theorem local_foundation_iff_all_reachable {α : Type u} (C : Region α) (D : α → α → Prop) :
    LocalFoundation C D ↔ Sub C (RootReachable C D) := by
  classical
  constructor
  · intro foundation x hx
    by_cases hparent : ∃ y, Parents C D x y
    · exact foundation x hx hparent
    · have root : Roots C D x := ⟨hx, fun y hy => hparent ⟨y, hy⟩⟩
      exact ⟨x, root, InternalPath.refl x hx⟩
  · intro h x hx _
    exact h hx

/-- Finite root-to-node paths indexed by their number of edges. -/
inductive RootLength {α : Type u} (C : Region α) (D : α → α → Prop) : Nat → α → Prop where
  | root (x : α) : Roots C D x → RootLength C D 0 x
  | step {n y x} : RootLength C D n y → C x → D y x → RootLength C D (n+1) x

theorem reachable_has_length {α : Type u} {C : Region α} {D : α → α → Prop}
    {x : α} (h : RootReachable C D x) : ∃ n, RootLength C D n x := by
  obtain ⟨b, hb, hp⟩ := h
  induction hp with
  | refl _ => exact ⟨0, RootLength.root b hb⟩
  | step path hx edge ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, RootLength.step hn hx edge⟩

theorem length_carrier {α : Type u} {C : Region α} {D : α → α → Prop}
    {n : Nat} {x : α} (h : RootLength C D n x) : C x := by
  cases h with
  | root _ hr => exact hr.1
  | step _ hc _ => exact hc

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

noncomputable def RootRank {α : Type u} (C : Region α) (D : α → α → Prop) (x : α) : Nat := by
  classical
  exact if h : ∃ n, RootLength C D n x then Classical.choose (exists_min_nat _ h) else 0

theorem root_rank_spec {α : Type u} {C : Region α} {D : α → α → Prop} {x : α}
    (h : ∃ n, RootLength C D n x) :
    RootLength C D (RootRank C D x) x ∧
      ∀ m, m < RootRank C D x → ¬ RootLength C D m x := by
  classical
  simpa [RootRank, h] using Classical.choose_spec (exists_min_nat (fun n => RootLength C D n x) h)

theorem nonroot_length_predecessor {α : Type u} {C : Region α} {D : α → α → Prop}
    {n : Nat} {x : α} (path : RootLength C D n x) (notRoot : ¬ Roots C D x) :
    ∃ y m, Parents C D x y ∧ n = m + 1 ∧ RootLength C D m y := by
  cases path with
  | root _ hr => exact False.elim (notRoot hr)
  | @step m y x path hx edge =>
    exact ⟨y, m, ⟨length_carrier path, edge⟩, rfl, path⟩

theorem ranked_parent_exists {α : Type u} {C : Region α} {D : α → α → Prop} {x : α}
    (reach : RootReachable C D x) (notRoot : ¬ Roots C D x) :
    ∃ y, Parents C D x y ∧ RootRank C D y < RootRank C D x := by
  have spec := root_rank_spec (reachable_has_length reach)
  obtain ⟨y, n, hp, heq, path⟩ := nonroot_length_predecessor spec.1 notRoot
  have yspec := root_rank_spec ⟨n, path⟩
  have hnot : ¬ n < RootRank C D y := by
    intro hlt
    exact yspec.2 n hlt path
  have hle : RootRank C D y ≤ n := Nat.le_of_not_gt hnot
  rw [heq]
  exact ⟨y, hp, Nat.lt_succ_of_le hle⟩

noncomputable def ForestMechanism {α : Type u} (C : Region α) (D : α → α → Prop)
    (x : α) (S : Region α) : Prop := by
  classical
  exact if Roots C D x then True
    else if h : ∃ y, Parents C D x y ∧ RootRank C D y < RootRank C D x
      then S (Classical.choose h) else False

theorem forest_mechanism_admissible {α : Type u} {C : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) : Mechanism C D (ForestMechanism C D) := by
  classical
  intro x hx
  by_cases hr : Roots C D x
  · simp [ForestMechanism, hr, hr.2]
  · have hp := ranked_parent_exists (reach hx) hr
    simp only [ForestMechanism, hr, hp, ↓reduceIte, ↓reduceDIte]
    have chosen := Classical.choose_spec hp
    constructor
    · intro A B hAB h
      exact hAB h
    constructor
    · constructor
      · intro h; exact False.elim h
      · intro h; exact False.elim (h _ chosen.1)
    · exact chosen.1

theorem forest_solutions_equal {α : Type u} {C U X Y : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) (ctx : Sub U (Roots C D))
    (fixedX : Fixed (Step C D (ForestMechanism C D) U) X)
    (fixedY : Fixed (Step C D (ForestMechanism C D) U) Y) : X = Y := by
  classical
  have xc : Sub X C := contextual_fixed_carrier ctx fixedX
  have yc : Sub Y C := contextual_fixed_carrier ctx fixedY
  have agree : ∀ n : Nat, ∀ x, C x → RootRank C D x = n → (X x ↔ Y x) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxC heq
      by_cases root : Roots C D x
      · exact (contextual_fixed_roots ctx fixedX x root).trans
          (contextual_fixed_roots ctx fixedY x root).symm
      · have hp := ranked_parent_exists (reach hxC) root
        let y := Classical.choose hp
        have hy := Classical.choose_spec hp
        have hlt : RootRank C D y < n := by rw [← heq]; exact hy.2
        have xy : X y ↔ Y y := ih (RootRank C D y) hlt y hy.1.1 rfl
        have notU : ¬ U x := fun hu => root (ctx hu)
        have xeq : X x ↔ X y := by
          constructor
          · intro hx
            have h : Step C D (ForestMechanism C D) U X x := by rw [fixedX]; exact hx
            rcases h with hu | ⟨_, _, gate⟩
            · exact False.elim (notU hu)
            · simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte] at gate
              exact gate.1
          · intro hyX
            have h : Step C D (ForestMechanism C D) U X x := by
              apply Or.inr
              refine ⟨hxC, ⟨y, hy.1⟩, ?_⟩
              simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte]
              exact ⟨hyX, hy.1⟩
            rw [fixedX] at h
            exact h
        have yeq : Y x ↔ Y y := by
          constructor
          · intro hx
            have h : Step C D (ForestMechanism C D) U Y x := by rw [fixedY]; exact hx
            rcases h with hu | ⟨_, _, gate⟩
            · exact False.elim (notU hu)
            · simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte] at gate
              exact gate.1
          · intro hyY
            have h : Step C D (ForestMechanism C D) U Y x := by
              apply Or.inr
              refine ⟨hxC, ⟨y, hy.1⟩, ?_⟩
              simp only [ForestMechanism, root, hp, ↓reduceIte, ↓reduceDIte]
              exact ⟨hyY, hy.1⟩
            rw [fixedY] at h
            exact h
        exact xeq.trans (xy.trans yeq.symm)
  funext x
  apply propext
  by_cases hc : C x
  · exact agree (RootRank C D x) x hc rfl
  · exact ⟨fun hx => False.elim (hc (xc hx)), fun hy => False.elim (hc (yc hy))⟩

theorem forest_copy_every_context_unique {α : Type u} {C : Region α} {D : α → α → Prop}
    (reach : Sub C (RootReachable C D)) : ContextDeterminate C D (ForestMechanism C D) := by
  intro U ctx
  have adm := forest_mechanism_admissible reach
  obtain ⟨X, _, fixed⟩ := contextual_solution_exists adm ctx
  refine ⟨X, fixed, ?_⟩
  intro Y fixedY
  exact forest_solutions_equal reach ctx fixedY fixed

theorem some_mechanism_every_context_unique_iff_local_foundation {α : Type u}
    (C : Region α) (D : α → α → Prop) :
    (∃ f, Mechanism C D f ∧ ContextDeterminate C D f) ↔ LocalFoundation C D := by
  constructor
  · rintro ⟨f, adm, all⟩
    apply (local_foundation_iff_all_reachable C D).mpr
    let U : Region α := fun _ => False
    have ctx : Sub U (Roots C D) := by intro x h; exact False.elim h
    obtain ⟨X, hX, unique⟩ := all U ctx
    have hT : Sub C (Determined C (Step C D f U)) := by
      intro x hx
      apply (determined_iff_fixed_agreement adm ctx hx).mpr
      intro Y Z hY hZ
      have eqY := unique Y hY
      have eqZ := unique Z hZ
      rw [eqY, eqZ]
    exact (some_context_determination_iff_reachable ctx).mp ⟨f, adm, hT⟩
  · intro foundation
    have reach := (local_foundation_iff_all_reachable C D).mp foundation
    exact ⟨ForestMechanism C D, forest_mechanism_admissible reach,
      forest_copy_every_context_unique reach⟩

def WellFoundedOn {α : Type u} (C : Region α) (D : α → α → Prop) : Prop :=
  ∀ x, C x → Acc (RestrictedEdge C D) x

theorem accessible_carrier_iff_well_founded {α : Type u} (C : Region α) (D : α → α → Prop) :
    Sub C (AccessibleRegion C D) ↔ WellFoundedOn C D := by
  constructor
  · intro h x hx; exact (h hx).2
  · intro h x hx; exact ⟨hx, h x hx⟩

theorem whole_determined_iff_unique {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    Sub C (Determined C (Step C D f U)) ↔ UniqueFixed (Step C D f U) := by
  constructor
  · intro determined
    obtain ⟨X, _, fixed⟩ := contextual_solution_exists adm ctx
    refine ⟨X, fixed, ?_⟩
    intro Y fixedY
    have xc := contextual_fixed_carrier ctx fixed
    have yc := contextual_fixed_carrier ctx fixedY
    funext x
    apply propext
    by_cases hc : C x
    · exact (determined_iff_fixed_agreement adm ctx hc).mp (determined hc) Y X fixedY fixed
    · exact ⟨fun hy => False.elim (hc (yc hy)), fun hx => False.elim (hc (xc hx))⟩
  · rintro ⟨X, fixed, unique⟩ x hx
    apply (determined_iff_fixed_agreement adm ctx hx).mpr
    intro Y Z fixedY fixedZ
    rw [unique Y fixedY, unique Z fixedZ]

theorem some_relevant_context_unique_iff_local_foundation {α : Type u}
    {C U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ UniqueFixed (Step C D f U)) ↔
      LocalFoundation C D := by
  rw [local_foundation_iff_all_reachable]
  constructor
  · rintro ⟨f, adm, rel, uniq⟩
    apply (some_relevant_context_determination_iff_reachable ctx).mp
    exact ⟨f, adm, rel, (whole_determined_iff_unique adm ctx).mpr uniq⟩
  · intro reach
    obtain ⟨f, adm, rel, det⟩ := (some_relevant_context_determination_iff_reachable ctx).mpr reach
    exact ⟨f, adm, rel, (whole_determined_iff_unique adm ctx).mp det⟩

theorem some_context_unique_iff_local_foundation {α : Type u}
    {C U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ UniqueFixed (Step C D f U)) ↔ LocalFoundation C D := by
  constructor
  · rintro ⟨f, adm, uniq⟩
    apply (local_foundation_iff_all_reachable C D).mpr
    exact (some_context_determination_iff_reachable ctx).mp
      ⟨f, adm, (whole_determined_iff_unique adm ctx).mpr uniq⟩
  · intro hf
    obtain ⟨f, adm, _, uniq⟩ := (some_relevant_context_unique_iff_local_foundation ctx).mpr hf
    exact ⟨f, adm, uniq⟩

theorem every_relevant_context_unique_iff_well_founded {α : Type u}
    {C U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∀ f, Mechanism C D f → Relevant C D f → UniqueFixed (Step C D f U)) ↔ WellFoundedOn C D := by
  rw [← accessible_carrier_iff_well_founded]
  constructor
  · intro h
    apply (every_relevant_context_determination_iff_accessible ctx).mp
    intro f adm rel
    exact (whole_determined_iff_unique adm ctx).mpr (h f adm rel)
  · intro h f adm rel
    apply (whole_determined_iff_unique adm ctx).mp
    exact ((every_relevant_context_determination_iff_accessible ctx).mpr h) f adm rel

theorem every_context_unique_iff_well_founded {α : Type u}
    {C U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∀ f, Mechanism C D f → UniqueFixed (Step C D f U)) ↔ WellFoundedOn C D := by
  rw [← accessible_carrier_iff_well_founded]
  constructor
  · intro h
    apply (every_context_determination_iff_accessible ctx).mp
    intro f adm
    exact (whole_determined_iff_unique adm ctx).mpr (h f adm)
  · intro h f adm
    apply (whole_determined_iff_unique adm ctx).mp
    exact ((every_context_determination_iff_accessible ctx).mpr h) f adm

theorem every_mechanism_every_context_unique_iff_well_founded {α : Type u}
    (C : Region α) (D : α → α → Prop) :
    (∀ f, Mechanism C D f → ContextDeterminate C D f) ↔ WellFoundedOn C D := by
  constructor
  · intro h
    let U : Region α := fun _ => False
    have ctx : Sub U (Roots C D) := by intro x bad; exact False.elim bad
    apply (every_context_unique_iff_well_founded ctx).mp
    intro f adm
    exact h f adm U ctx
  · intro hw f adm U ctx
    exact (every_context_unique_iff_well_founded ctx).mpr hw f adm

theorem every_relevant_mechanism_every_context_unique_iff_well_founded {α : Type u}
    (C : Region α) (D : α → α → Prop) :
    (∀ f, Mechanism C D f → Relevant C D f → ContextDeterminate C D f) ↔ WellFoundedOn C D := by
  constructor
  · intro h
    let U : Region α := fun _ => False
    have ctx : Sub U (Roots C D) := by intro x bad; exact False.elim bad
    apply (every_relevant_context_unique_iff_well_founded ctx).mp
    intro f adm rel
    exact h f adm rel U ctx
  · intro hw f adm rel U ctx
    exact (every_relevant_context_unique_iff_well_founded ctx).mpr hw f adm rel

end DeterminationPatterns
