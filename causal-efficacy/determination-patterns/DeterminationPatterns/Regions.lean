module
public import DeterminationPatterns.Necessity
@[expose] public section
namespace DeterminationPatterns
universe u

/-- Source region criterion: carrier and root containment, internal root reach,
and closure under the universal-parent operator. -/
def RegionConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (K : Region α) : Prop :=
  Sub K C ∧ Sub (Roots C D) K ∧ InternalReach K D (Roots C D) = K ∧
  (∀ x, C x → (∀ y, Parents C D x y → K y) → K x)

theorem path_weaken {α : Type u} {A B : Region α} {D : α → α → Prop}
    (hAB : Sub A B) {x y : α} (p : InternalPath A D x y) : InternalPath B D x y := by
  induction p with
  | refl hx => exact InternalPath.refl _ (hAB hx)
  | step _ hx edge ih => exact InternalPath.step ih (hAB hx) edge

theorem reach_weaken {α : Type u} {A B S T : Region α} {D : α → α → Prop}
    (hAB : Sub A B) (hST : Sub S T) : Sub (InternalReach A D S) (InternalReach B D T) := by
  intro x ⟨b, hb, p⟩
  exact ⟨b, hST hb, path_weaken hAB p⟩

theorem pattern_region_conditions {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (cond : PatternConditions C D U L Z Q) (ctx : Sub U (Roots C D)) :
    RegionConditions C D (fun x => L x ∨ Z x) := by
  classical
  let K : Region α := fun x => L x ∨ Z x
  have kc : Sub K C := by
    intro x h
    rcases h with hl | hz
    · exact (part.1 x).mpr (Or.inl hl)
    · exact (part.1 x).mpr (Or.inr (Or.inl hz))
  have roots : Sub (Roots C D) K := by
    intro x hr
    by_cases hu : U x
    · exact Or.inl (cond.1 hu)
    · exact Or.inr (cond.2.1 ⟨hr, hu⟩)
  have kreached : InternalReach K D (Roots C D) = K := by
    apply funext
    intro x
    apply propext
    constructor
    · intro ⟨_, _, p⟩; exact path_target p
    · intro hx
      rcases hx with hl | hz
      · have h : InternalReach L D U x := by rw [cond.2.2.1]; exact hl
        exact reach_weaken (fun _ h => Or.inl h) ctx h
      · have h : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) x := by
          rw [cond.2.2.2.1]; exact hz
        exact reach_weaken (fun _ h => Or.inr h) (fun _ h => h.1) h
  have closed : ∀ x, C x → (∀ y, Parents C D x y → K y) → K x := by
    intro x hx allp
    apply Classical.byContradiction
    intro hnot
    have hq : Q x := by
      rcases (part.1 x).mp hx with hl | hz | hq
      · exact False.elim (hnot (Or.inl hl))
      · exact False.elim (hnot (Or.inr hz))
      · exact hq
    obtain ⟨y, hp, hqY⟩ := cond.2.2.2.2 x hq
    rcases allp y hp with hl | hz
    · exact (part.2.2.1 y) ⟨hl, hqY⟩
    · exact (part.2.2.2 y) ⟨hz, hqY⟩
  exact ⟨kc, roots, kreached, closed⟩

theorem extremal_status_partition {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    StatusPartition C (Least (Step C D f U))
      (fun x => C x ∧ ¬ Greatest (Step C D f U) x)
      (fun x => Greatest (Step C D f U) x ∧ ¬ Least (Step C D f U) x) := by
  classical
  let F := Step C D f U
  let L := Least F
  let G := Greatest F
  have lf : Fixed F L := least_fixed (step_monotone adm U)
  have gf : Fixed F G := greatest_fixed (step_monotone adm U)
  have lc : Sub L C := contextual_fixed_carrier ctx lf
  have gc : Sub G C := contextual_fixed_carrier ctx gf
  have lg : Sub L G := (fixed_bounds gf).1
  constructor
  · intro x
    constructor
    · intro hc
      by_cases hl : L x
      · exact Or.inl hl
      · by_cases hg : G x
        · exact Or.inr (Or.inr ⟨hg, hl⟩)
        · exact Or.inr (Or.inl ⟨hc, hg⟩)
    · intro h
      rcases h with hl | ⟨hc, _⟩ | ⟨hg, _⟩
      · exact lc hl
      · exact hc
      · exact gc hg
  · constructor
    · intro x ⟨hl, _, hn⟩; exact hn (lg hl)
    · constructor
      · intro x ⟨hl, _, hn⟩; exact hn hl
      · intro x ⟨⟨_, hn⟩, hg, _⟩; exact hn hg

theorem determined_region_conditions {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    RegionConditions C D (Determined C (Step C D f U)) := by
  classical
  let F := Step C D f U
  let L := Least F
  let G := Greatest F
  let Z : Region α := fun x => C x ∧ ¬ G x
  let Q : Region α := fun x => G x ∧ ¬ L x
  have part : StatusPartition C L Z Q := extremal_status_partition adm ctx
  have gf : Fixed F G := greatest_fixed (step_monotone adm U)
  have gc : Sub G C := contextual_fixed_carrier ctx gf
  have high : G = (fun x => C x ∧ ¬ Z x) := by
    funext x
    apply propext
    constructor
    · intro hg
      exact ⟨gc hg, fun h => h.2 hg⟩
    · intro ⟨_, hn⟩
      apply Classical.byContradiction
      intro hng
      exact hn ⟨by assumption, hng⟩
  have cond : PatternConditions C D U L Z Q :=
    realized_pattern_necessary part ctx adm rfl high
  exact pattern_region_conditions part cond ctx

theorem path_source {α : Type u} {A : Region α} {D : α → α → Prop}
    {b x : α} (h : InternalPath A D b x) : A b := by
  induction h with
  | refl hx => exact hx
  | step _ _ _ ih => exact ih

theorem reach_step {α : Type u} {K U : Region α} {D : α → α → Prop}
    {y x : α} (hy : InternalReach K D U y) (hx : K x) (edge : D y x) :
    InternalReach K D U x := by
  obtain ⟨b, hb, hp⟩ := hy
  exact ⟨b, hb, InternalPath.step hp hx edge⟩

theorem path_in_reached {α : Type u} {K U : Region α} {D : α → α → Prop}
    {b x : α} (p : InternalPath K D b x) (hb : U b) :
    InternalPath (InternalReach K D U) D b x := by
  induction p with
  | refl hk => exact InternalPath.refl _ ⟨_, hb, InternalPath.refl _ hk⟩
  | step path hx edge ih =>
    exact InternalPath.step ih ⟨_, hb, InternalPath.step path hx edge⟩ edge

theorem path_outside_reached {α : Type u} {K U : Region α} {D : α → α → Prop}
    {b x : α} (p : InternalPath K D b x) :
    ¬ InternalReach K D U x →
      InternalPath (fun z => K z ∧ ¬ InternalReach K D U z) D b x := by
  induction p with
  | refl hk =>
    intro hn
    exact InternalPath.refl _ ⟨hk, hn⟩
  | @step y x path hx edge ih =>
    intro hn
    have hy : ¬ InternalReach K D U y := by
      intro hr
      exact hn (reach_step hr hx edge)
    exact InternalPath.step (ih hy) ⟨hx, hn⟩ edge

theorem region_conditions_sufficient {α : Type u} {C K U : Region α}
    {D : α → α → Prop} (reg : RegionConditions C D K)
    (ctx : Sub U (Roots C D)) :
    ∃ f, Mechanism C D f ∧ Relevant C D f ∧ Determined C (Step C D f U) = K := by
  classical
  let L := InternalReach K D U
  let Z : Region α := fun x => K x ∧ ¬ L x
  let Q : Region α := fun x => C x ∧ ¬ K x
  have lk : Sub L K := by intro x ⟨_, _, hp⟩; exact path_target hp
  have uk : Sub U K := by intro x hu; exact reg.2.1 (ctx hu)
  have ul : Sub U L := by
    intro x hu
    exact ⟨x, hu, InternalPath.refl x (uk hu)⟩
  have part : StatusPartition C L Z Q := by
    constructor
    · intro x
      constructor
      · intro hc
        by_cases hk : K x
        · by_cases hl : L x
          · exact Or.inl hl
          · exact Or.inr (Or.inl ⟨hk, hl⟩)
        · exact Or.inr (Or.inr ⟨hc, hk⟩)
      · intro h
        rcases h with hl | ⟨hk, _⟩ | ⟨hc, _⟩
        · exact reg.1 (lk hl)
        · exact reg.1 hk
        · exact hc
    · constructor
      · intro x ⟨hl, _, hnot⟩; exact hnot hl
      · constructor
        · intro x ⟨hl, _, hnot⟩; exact hnot (lk hl)
        · intro x ⟨⟨hk, _⟩, _, hnot⟩; exact hnot hk
  have rootZ : Sub (fun x => Roots C D x ∧ ¬ U x) Z := by
    intro x ⟨hr, hn⟩
    refine ⟨reg.2.1 hr, ?_⟩
    intro hL
    rcases path_last_or_seed hL with hu | ⟨y, hyK, edge⟩
    · exact hn hu
    · exact hr.2 y ⟨reg.1 hyK, edge⟩
  have reachL : InternalReach L D U = L := by
    apply funext
    intro x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro h
      obtain ⟨b, hb, hp⟩ := h
      exact ⟨b, hb, path_in_reached hp hb⟩
  have reachZ : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    apply funext
    intro x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨hk, hnL⟩
      have hr : InternalReach K D (Roots C D) x := by rw [reg.2.2.1]; exact hk
      obtain ⟨b, hbRoot, hp⟩ := hr
      have zp : InternalPath Z D b x := path_outside_reached hp hnL
      have hbNotL : ¬ L b := (path_source zp).2
      have hbNotU : ¬ U b := fun hu => hbNotL (ul hu)
      exact ⟨b, ⟨hbRoot, hbNotU⟩, zp⟩
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y := by
    intro x ⟨hc, hnK⟩
    apply Classical.byContradiction
    intro hn
    apply hnK
    apply reg.2.2.2 x hc
    intro y hp
    apply Classical.byContradiction
    intro hyNotK
    exact hn ⟨y, hp, hp.1, hyNotK⟩
  have cond : PatternConditions C D U L Z Q := ⟨ul, rootZ, reachL, reachZ, qp⟩
  have witness := pattern_witness_extrema part cond ctx
  refine ⟨StatusMechanism C D L Z Q, witness.1, witness.2.1, ?_⟩
  funext x
  apply propext
  unfold Determined
  rw [witness.2.2.1, witness.2.2.2]
  constructor
  · intro h
    rcases h with hl | ⟨hc, hn⟩
    · exact lk hl
    · apply Classical.byContradiction
      intro hnK
      exact hn ⟨hc, fun hz => hnK hz.1⟩
  · intro hk
    by_cases hl : L x
    · exact Or.inl hl
    · exact Or.inr ⟨reg.1 hk, fun h => h.2 ⟨hk, hl⟩⟩

theorem exact_relevant_region_realization {α : Type u} {C K U : Region α}
    {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Determined C (Step C D f U) = K) ↔
      RegionConditions C D K := by
  constructor
  · rintro ⟨f, adm, _, eq⟩
    have h := determined_region_conditions adm ctx
    rw [eq] at h
    exact h
  · exact fun h => region_conditions_sufficient h ctx

theorem exact_region_realization {α : Type u} {C K U : Region α}
    {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Determined C (Step C D f U) = K) ↔
      RegionConditions C D K := by
  constructor
  · rintro ⟨f, adm, eq⟩
    have h := determined_region_conditions adm ctx
    rw [eq] at h
    exact h
  · intro h
    obtain ⟨f, adm, _, eq⟩ := region_conditions_sufficient h ctx
    exact ⟨f, adm, eq⟩

theorem attainable_regions_context_independent {α : Type u} {C K U V : Region α}
    {D : α → α → Prop} (ctxU : Sub U (Roots C D)) (ctxV : Sub V (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Determined C (Step C D f U) = K) ↔
    (∃ g, Mechanism C D g ∧ Relevant C D g ∧ Determined C (Step C D g V) = K) :=
  (exact_relevant_region_realization ctxU).trans (exact_relevant_region_realization ctxV).symm

end DeterminationPatterns
