module
public import DeterminationPatterns.Regions
@[expose] public section
namespace DeterminationPatterns
universe u

/-- Finite reachability from carrier roots. -/
def RootReachable {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  InternalReach C D (Roots C D)

/-- Carrier members accessible for the carrier-restricted predecessor relation. -/
def AccessibleRegion {α : Type u} (C : Region α) (D : α → α → Prop) : Region α :=
  fun x => C x ∧ Acc (RestrictedEdge C D) x

theorem root_reachable_conditions {α : Type u} (C : Region α) (D : α → α → Prop) :
    RegionConditions C D (RootReachable C D) := by
  classical
  let R := RootReachable C D
  have rc : Sub R C := by intro x ⟨_, _, hp⟩; exact path_target hp
  have roots : Sub (Roots C D) R := by
    intro x hx
    exact ⟨x, hx, InternalPath.refl x hx.1⟩
  have reach : InternalReach R D (Roots C D) = R := by
    funext x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨b, hb, hp⟩
      exact ⟨b, hb, path_in_reached hp hb⟩
  have closed : ∀ x, C x → (∀ y, Parents C D x y → R y) → R x := by
    intro x hx allp
    by_cases hp : ∃ y, Parents C D x y
    · obtain ⟨y, hy⟩ := hp
      exact reach_step (allp y hy) hx hy.2
    · exact roots ⟨hx, fun y hy => hp ⟨y, hy⟩⟩
  exact ⟨rc, roots, reach, closed⟩

theorem accessible_subset_region {α : Type u} {C K : Region α} {D : α → α → Prop}
    (reg : RegionConditions C D K) : Sub (AccessibleRegion C D) K := by
  intro x ⟨hxC, hxAcc⟩
  induction hxAcc with
  | intro x hacc ih =>
    apply reg.2.2.2 x hxC
    intro y hy
    exact ih y ⟨hy.1, hxC, hy.2⟩ hy.1

theorem accessible_region_conditions {α : Type u} (C : Region α) (D : α → α → Prop) :
    RegionConditions C D (AccessibleRegion C D) := by
  classical
  let W := AccessibleRegion C D
  have wc : Sub W C := by intro x hx; exact hx.1
  have roots : Sub (Roots C D) W := by
    intro x ⟨hc, hno⟩
    refine ⟨hc, Acc.intro x ?_⟩
    intro y ⟨hyC, _, hyD⟩
    exact False.elim (hno y ⟨hyC, hyD⟩)
  have reachable : ∀ x, Acc (RestrictedEdge C D) x → C x → InternalReach W D (Roots C D) x := by
    intro x ha
    induction ha with
    | intro x hacc ih =>
      intro hc
      have wx : W x := ⟨hc, Acc.intro x hacc⟩
      by_cases hp : ∃ y, Parents C D x y
      · obtain ⟨y, hy⟩ := hp
        have edge : RestrictedEdge C D y x := ⟨hy.1, hc, hy.2⟩
        exact reach_step (ih y edge hy.1) wx hy.2
      · have root : Roots C D x := ⟨hc, fun y hy => hp ⟨y, hy⟩⟩
        exact ⟨x, root, InternalPath.refl x wx⟩
  have reach : InternalReach W D (Roots C D) = W := by
    funext x
    apply propext
    constructor
    · intro ⟨_, _, hp⟩; exact path_target hp
    · intro ⟨hc, ha⟩; exact reachable x ha hc
  have closed : ∀ x, C x → (∀ y, Parents C D x y → W y) → W x := by
    intro x hc allp
    refine ⟨hc, Acc.intro x ?_⟩
    intro y ⟨hyC, _, hyD⟩
    exact (allp y ⟨hyC, hyD⟩).2
  exact ⟨wc, roots, reach, closed⟩

theorem region_subset_reachable {α : Type u} {C K : Region α} {D : α → α → Prop}
    (reg : RegionConditions C D K) : Sub K (RootReachable C D) := by
  intro x hx
  have h : InternalReach K D (Roots C D) x := by rw [reg.2.2.1]; exact hx
  exact reach_weaken reg.1 (fun _ h => h) h

theorem some_relevant_context_determination_iff_reachable {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Sub T (Determined C (Step C D f U))) ↔
      Sub T (RootReachable C D) := by
  constructor
  · rintro ⟨f, adm, _, hT⟩
    have reg := determined_region_conditions adm ctx
    intro x hx
    exact region_subset_reachable reg (hT hx)
  · intro hT
    obtain ⟨f, adm, rel, eq⟩ := region_conditions_sufficient (root_reachable_conditions C D) ctx
    refine ⟨f, adm, rel, ?_⟩
    rw [eq]
    exact hT

theorem some_context_determination_iff_reachable {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Sub T (Determined C (Step C D f U))) ↔
      Sub T (RootReachable C D) := by
  constructor
  · rintro ⟨f, adm, hT⟩
    have reg := determined_region_conditions adm ctx
    intro x hx
    exact region_subset_reachable reg (hT hx)
  · intro hT
    obtain ⟨f, adm, _, h⟩ := (some_relevant_context_determination_iff_reachable ctx).mpr hT
    exact ⟨f, adm, h⟩

theorem every_relevant_context_determination_iff_accessible {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∀ f, Mechanism C D f → Relevant C D f → Sub T (Determined C (Step C D f U))) ↔
      Sub T (AccessibleRegion C D) := by
  constructor
  · intro hall
    obtain ⟨f, adm, rel, eq⟩ := region_conditions_sufficient (accessible_region_conditions C D) ctx
    have h := hall f adm rel
    rw [eq] at h
    exact h
  · intro hT f adm _
    have reg := determined_region_conditions adm ctx
    intro x hx
    exact accessible_subset_region reg (hT hx)

theorem every_context_determination_iff_accessible {α : Type u}
    {C T U : Region α} {D : α → α → Prop} (ctx : Sub U (Roots C D)) :
    (∀ f, Mechanism C D f → Sub T (Determined C (Step C D f U))) ↔
      Sub T (AccessibleRegion C D) := by
  constructor
  · intro hall
    apply (every_relevant_context_determination_iff_accessible ctx).mp
    intro f adm _
    exact hall f adm
  · intro hT f adm
    have reg := determined_region_conditions adm ctx
    intro x hx
    exact accessible_subset_region reg (hT hx)

end DeterminationPatterns
