module
import Init
@[expose] public section


/-! Self-contained statement and proof surface for contextual determination bounds. -/
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

/-- The contextual update includes every element of `U` and evaluates each
non-root carrier vertex on its currently active parents. If `U` is contained
in the roots, it selects the roots that are turned on. -/
def Step {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U X : Region α) : Region α :=
  fun x => U x ∨ (C x ∧ (∃ y, Parents C D x y) ∧
    f x (fun y => X y ∧ Parents C D x y))

/-- Inclusion of input regions implies inclusion of their images. -/
def Monotone {α : Type u} (F : Region α → Region α) : Prop :=
  ∀ A B, Sub A B → Sub (F A) (F B)

/-- Intersection of all pre-fixed regions of `F`. -/
def Least {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∀ S, Sub (F S) S → S x

/-- Union of all post-fixed regions of `F`. -/
def Greatest {α : Type u} (F : Region α → Region α) : Region α :=
  fun x => ∃ S, Sub S (F S) ∧ S x

/-- `X` is unchanged by `F`. -/
def Fixed {α : Type u} (F : Region α → Region α) (X : Region α) : Prop := F X = X


/-- The least region and carrier members outside the greatest region. -/
def Determined {α : Type u} (C : Region α) (F : Region α → Region α) : Region α :=
  fun x => Least F x ∨ (C x ∧ ¬ Greatest F x)

theorem step_monotone {α : Type u} {C : Region α} {D : α → α → Prop}
    {f : α → Region α → Prop} (h : Mechanism C D f) (U : Region α) :
    Monotone (Step C D f U) := by
  intro A B hAB x hx
  rcases hx with hu | ⟨hc, hp, hf⟩
  · exact Or.inl hu
  · exact Or.inr ⟨hc, hp, (h x hc).1 _ _ (fun _ hz => ⟨hAB hz.1, hz.2⟩) hf⟩

theorem least_le {α : Type u} (F : Region α → Region α) (S : Region α)
    (h : Sub (F S) S) : Sub (Least F) S := by
  intro x hx
  exact hx S h

theorem le_greatest {α : Type u} (F : Region α → Region α) (S : Region α)
    (h : Sub S (F S)) : Sub S (Greatest F) := by
  intro x hx
  exact ⟨S, h, hx⟩

theorem least_fixed {α : Type u} {F : Region α → Region α} (h : Monotone F) :
    Fixed F (Least F) := by
  have pre : Sub (F (Least F)) (Least F) := by
    intro x hx S hS
    exact hS (h (Least F) S (least_le F S hS) hx)
  have post : Sub (Least F) (F (Least F)) :=
    least_le F (F (Least F)) (h _ _ pre)
  apply funext
  intro x
  exact propext ⟨fun hx => pre hx, fun hx => post hx⟩

theorem greatest_fixed {α : Type u} {F : Region α → Region α} (h : Monotone F) :
    Fixed F (Greatest F) := by
  have post : Sub (Greatest F) (F (Greatest F)) := by
    intro x hx
    rcases hx with ⟨S, hS, hsx⟩
    exact h S (Greatest F) (le_greatest F S hS) (hS hsx)
  have pre : Sub (F (Greatest F)) (Greatest F) :=
    le_greatest F (F (Greatest F)) (h _ _ post)
  apply funext
  intro x
  exact propext ⟨fun hx => pre hx, fun hx => post hx⟩

theorem fixed_bounds {α : Type u} {F : Region α → Region α} {X : Region α}
    (hx : Fixed F X) : Sub (Least F) X ∧ Sub X (Greatest F) := by
  have pre : Sub (F X) X := by intro x h; rw [hx] at h; exact h
  have post : Sub X (F X) := by intro x h; rw [hx]; exact h
  exact ⟨least_le F X pre, le_greatest F X post⟩


end DeterminationPatterns


namespace DeterminationPatterns
universe u

/-- A finite path whose vertices all belong to A, including its endpoints. -/
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


end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- The carrier is exactly the disjoint union of the three statuses. -/
def StatusPartition {α : Type u} (C L Z Q : Region α) : Prop :=
  (∀ x, C x ↔ L x ∨ Z x ∨ Q x) ∧
  (∀ x, ¬ (L x ∧ Z x)) ∧ (∀ x, ¬ (L x ∧ Q x)) ∧ (∀ x, ¬ (Z x ∧ Q x))

/-- `U` lies in `L` and all roots outside `U` lie in `Z`; `L` is exactly
the set reachable from `U` through `L`, `Z` is exactly the set reachable
from roots outside `U` through `Z`, and every `Q` vertex has a `Q` parent.
The condition that `U` consists of roots is a separate assumption. -/
def PatternConditions {α : Type u} (C : Region α) (D : α → α → Prop)
    (U L Z Q : Region α) : Prop :=
  Sub U L ∧ Sub (fun x => Roots C D x ∧ ¬ U x) Z ∧
  InternalReach L D U = L ∧
  InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z ∧
  (∀ x, Q x → ∃ y, Parents C D x y ∧ Q y)

theorem contextual_fixed_carrier {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) : Sub X C := by
  intro x hx
  have hf : Step C D f U X x := by rw [fixed]; exact hx
  rcases hf with hu | ⟨hc, _, _⟩
  · exact (ctx hu).1
  · exact hc

theorem contextual_fixed_roots {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (_ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) :
    ∀ x, Roots C D x → (X x ↔ U x) := by
  intro x root
  constructor
  · intro hx
    have hf : Step C D f U X x := by rw [fixed]; exact hx
    rcases hf with hu | ⟨_, ⟨y, hy⟩, _⟩
    · exact hu
    · exact False.elim (root.2 y hy)
  · intro hu
    have hf : Step C D f U X x := Or.inl hu
    rw [fixed] at hf
    exact hf

theorem contextual_greatest_internal_zero_paths {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    InternalReach (fun x => C x ∧ ¬ Greatest (Step C D f U) x) D
      (fun x => Roots C D x ∧ ¬ U x) =
      (fun x => C x ∧ ¬ Greatest (Step C D f U) x) := by
  classical
  let F := Step C D f U
  let G := Greatest F
  let Z : Region α := fun x => C x ∧ ¬ G x
  let R := InternalReach Z D (fun x => Roots C D x ∧ ¬ U x)
  let Y : Region α := fun x => C x ∧ ¬ R x
  have hm : Monotone F := step_monotone adm U
  have gf : Fixed F G := greatest_fixed hm
  have gc : Sub G C := contextual_fixed_carrier ctx gf
  have rz : Sub R Z := by intro x h; obtain ⟨_, _, hp⟩ := h; exact path_target hp
  have gy : Sub G Y := by
    intro x hx
    refine ⟨gc hx, ?_⟩
    intro hr
    exact (rz hr).2 hx
  have post : Sub Y (F Y) := by
    intro x ⟨hxC, hxNotR⟩
    by_cases hxG : G x
    · have hFG : F G x := by rw [gf]; exact hxG
      exact hm G Y gy hFG
    · have hxZ : Z x := ⟨hxC, hxG⟩
      have hxNotU : ¬ U x := by
        intro hu
        have hFG : F G x := Or.inl hu
        rw [gf] at hFG
        exact hxG hFG
      have hparent : ∃ y, Parents C D x y := by
        apply Classical.byContradiction
        intro hnone
        have root : Roots C D x := ⟨hxC, fun y hy => hnone ⟨y, hy⟩⟩
        have rx : R x := ⟨x, ⟨root, hxNotU⟩, InternalPath.refl x hxZ⟩
        exact hxNotR rx
      have noR : ∀ y, Parents C D x y → ¬ R y := by
        intro y hyP hyR
        obtain ⟨b, hb, path⟩ := hyR
        have rx : R x := ⟨b, hb, InternalPath.step path hxZ hyP.2⟩
        exact hxNotR rx
      have inputs : (fun y => Y y ∧ Parents C D x y) = Parents C D x := by
        funext y
        apply propext
        constructor
        · intro h; exact h.2
        · intro hp; exact ⟨⟨hp.1, noR y hp⟩, hp⟩
      apply Or.inr
      refine ⟨hxC, hparent, ?_⟩
      rw [inputs]
      exact (adm x hxC).2.2
  have yz : Sub Y G := le_greatest F Y post
  apply funext
  intro x
  apply propext
  constructor
  · intro hr; exact rz hr
  · intro hx
    apply Classical.byContradiction
    intro hn
    exact hx.2 (yz ⟨hx.1, hn⟩)

theorem ambiguity_has_ambiguous_parent {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (_ctx : Sub U (Roots C D)) {x : α}
    (hxG : Greatest (Step C D f U) x) (hxNotL : ¬ Least (Step C D f U) x) :
    ∃ y, Parents C D x y ∧ Greatest (Step C D f U) y ∧
      ¬ Least (Step C D f U) y := by
  classical
  let F := Step C D f U
  let L := Least F
  let G := Greatest F
  have hm : Monotone F := step_monotone adm U
  have lf : Fixed F L := least_fixed hm
  have gf : Fixed F G := greatest_fixed hm
  have lg : Sub L G := (fixed_bounds gf).1
  apply Classical.byContradiction
  intro hn
  have eq : (fun y => L y ∧ Parents C D x y) = (fun y => G y ∧ Parents C D x y) := by
    funext y
    apply propext
    constructor
    · intro h; exact ⟨lg h.1, h.2⟩
    · intro h
      have hyL : L y := by
        apply Classical.byContradiction
        intro hnot
        exact hn ⟨y, h.2, h.1, hnot⟩
      exact ⟨hyL, h.2⟩
  have hfg : F G x := by rw [gf]; exact hxG
  have hfl : F L x := by
    rcases hfg with hu | ⟨hc, hp, hf⟩
    · exact Or.inl hu
    · apply Or.inr
      refine ⟨hc, hp, ?_⟩
      rw [eq]
      exact hf
  rw [lf] at hfl
  exact hxNotL hfl

/-- Any admissible mechanism realizing these extremal regions satisfies the
pattern conditions; edge relevance is not needed for this direction. -/
theorem realized_pattern_necessary {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (part : StatusPartition C L Z Q) (ctx : Sub U (Roots C D))
    (adm : Mechanism C D f) (low : Least (Step C D f U) = L)
    (high : Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) :
    PatternConditions C D U L Z Q := by
  classical
  let F := Step C D f U
  have lf : Fixed F L := by
    have h := least_fixed (step_monotone adm U)
    rw [low] at h
    exact h
  have gf : Fixed F (fun x => C x ∧ ¬ Z x) := by
    have h := greatest_fixed (step_monotone adm U)
    rw [high] at h
    exact h
  have zc : Sub Z C := by intro x hz; exact (part.1 x).mpr (Or.inr (Or.inl hz))
  have qc : Sub Q C := by intro x hq; exact (part.1 x).mpr (Or.inr (Or.inr hq))
  have ul : Sub U L := by
    intro x hu
    have h : F L x := Or.inl hu
    rw [lf] at h
    exact h
  have rootZ : Sub (fun x => Roots C D x ∧ ¬ U x) Z := by
    intro x ⟨hroot, hnot⟩
    have iff := contextual_fixed_roots ctx gf x hroot
    apply Classical.byContradiction
    intro hnz
    exact hnot (iff.mp ⟨hroot.1, hnz⟩)
  have lpath : InternalReach L D U = L := by
    have h := contextual_least_internal_paths adm ctx
    rw [low] at h
    exact h
  have zpath : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    have h := contextual_greatest_internal_zero_paths adm ctx
    rw [high] at h
    have zform : (fun x => C x ∧ ¬ (C x ∧ ¬ Z x)) = Z := by
      funext x
      apply propext
      constructor
      · intro ⟨hc, hn⟩
        apply Classical.byContradiction
        intro hnz
        exact hn ⟨hc, hnz⟩
      · intro hz
        exact ⟨zc hz, fun h => h.2 hz⟩
    rw [zform] at h
    exact h
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y := by
    intro x hxQ
    have hxNotL : ¬ L x := by intro hl; exact (part.2.2.1 x) ⟨hl, hxQ⟩
    have hxNotZ : ¬ Z x := by intro hz; exact (part.2.2.2 x) ⟨hz, hxQ⟩
    have hxG : Greatest F x := by rw [high]; exact ⟨qc hxQ, hxNotZ⟩
    have hxNotLeast : ¬ Least F x := by rw [low]; exact hxNotL
    obtain ⟨y, hyP, hyG, hyNotLeast⟩ := ambiguity_has_ambiguous_parent adm ctx hxG hxNotLeast
    have hyNotL : ¬ L y := by rw [← low]; exact hyNotLeast
    have hyNotZ : ¬ Z y := by rw [high] at hyG; exact hyG.2
    have hyQ : Q y := by
      rcases (part.1 y).mp hyP.1 with hyL | hyZ | hyQ
      · exact False.elim (hyNotL hyL)
      · exact False.elim (hyNotZ hyZ)
      · exact hyQ
    exact ⟨y, hyP, hyQ⟩
  exact ⟨ul, rootZ, lpath, zpath, qp⟩


end DeterminationPatterns

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

/-- Every admissible mechanism at a legal root context has a determinate region satisfying the exact region criterion. -/
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


end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- Dependency edges whose endpoints both lie in `A`. -/
def RestrictedEdge {α : Type u} (A : Region α) (D : α → α → Prop) : α → α → Prop :=
  fun y x => A y ∧ A x ∧ D y x

/-- Finite reachability from carrier roots. -/
def RootReachable {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  InternalReach C D (Roots C D)

/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x

theorem accessible_subset_region {α : Type u} {C K : Region α} {D : α → α → Prop}
    (reg : RegionConditions C D K) : Sub (AccessibleRegion C D) K := by
  intro x ⟨hxC, hxAcc⟩
  induction hxAcc with
  | intro x hacc ih =>
    apply reg.2.2.2 x hxC
    intro y hy
    exact ih y ⟨hy.1, hxC, hy.2⟩ hy.1

theorem region_subset_reachable {α : Type u} {C K : Region α} {D : α → α → Prop}
    (reg : RegionConditions C D K) : Sub K (RootReachable C D) := by
  intro x hx
  have h : InternalReach K D (Roots C D) x := by rw [reg.2.2.1]; exact hx
  exact reach_weaken reg.1 (fun _ h => h) h

/-- At every legal context and for every admissible mechanism, all accessible
vertices are determined and all determined vertices are root-reachable. -/
theorem contextual_determination_interval {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    Sub (AccessibleRegion C D) (Determined C (Step C D f U)) ∧
      Sub (Determined C (Step C D f U)) (RootReachable C D) := by
  have reg := determined_region_conditions adm ctx
  exact ⟨accessible_subset_region reg, region_subset_reachable reg⟩


end DeterminationPatterns
