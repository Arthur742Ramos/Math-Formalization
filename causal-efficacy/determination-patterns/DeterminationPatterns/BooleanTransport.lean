module
public import DeterminationPatterns.SourceInference
@[expose] public section
namespace DeterminationPatterns
universe u

abbrev BooleanRegion (α : Type u) := α → Bool

def BooleanSubset {α : Type u} (A B : BooleanRegion α) : Prop :=
  ∀ x, A x = true → B x = true

def BooleanParents {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (x : α) : BooleanRegion α := fun y => C y && D y x

def BooleanMechanism {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) : Prop :=
  ∀ x, C x = true →
    (∀ A B, BooleanSubset A B → f x A = true → f x B = true) ∧
    (f x (fun _ => false) = true ↔ ∀ y, BooleanParents C D x y = false) ∧
    f x (BooleanParents C D x) = true

theorem boolean_subset_bridge {α : Type u} (A B : BooleanRegion α) :
    BooleanSubset A B ↔ Sub (propRegion A) (propRegion B) := by
  constructor
  · intro h x hx; exact h x hx
  · intro h x hx; exact h hx

theorem boolean_parents_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool) (x : α) :
    propRegion (BooleanParents C D x) = Parents (propRegion C) (propRelation D) x := by
  funext y
  apply propext
  simp [propRegion, propRelation, propOf, BooleanParents, Parents, Bool.and_eq_true]

theorem boolean_empty_bridge {α : Type u} :
    boolRegion (fun _ : α => False) = (fun _ => false) := by
  funext x
  simp [boolRegion, boolOf]

theorem boolean_mechanism_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) :
    BooleanMechanism C D f ↔ Mechanism (propRegion C) (propRelation D) (fromBooleanMechanism f) := by
  classical
  have par (x : α) : boolRegion (Parents (propRegion C) (propRelation D) x) = BooleanParents C D x := by
    rw [← boolean_parents_bridge C D x, bool_prop_region]
  have none (x : α) : (∀ y, ¬ Parents (propRegion C) (propRelation D) x y) ↔
      ∀ y, BooleanParents C D x y = false := by
    constructor
    · intro h y
      have hy : ¬ propRegion (BooleanParents C D x) y := by rw [boolean_parents_bridge]; exact h y
      cases eq : BooleanParents C D x y <;> simp_all [propRegion, propOf]
    · intro h y hp
      have hy : propRegion (BooleanParents C D x) y := by rw [boolean_parents_bridge]; exact hp
      simp [propRegion, propOf, h y] at hy
  constructor
  · intro bm x hx
    have h := bm x hx
    constructor
    · intro A B sub hA
      apply h.1 (boolRegion A) (boolRegion B)
      · apply (boolean_subset_bridge _ _).mpr
        simpa only [prop_bool_region] using sub
      · exact hA
    constructor
    · rw [none x]
      simpa only [fromBooleanMechanism, propOf, boolean_empty_bridge] using h.2.1
    · simpa only [fromBooleanMechanism, propOf, par x] using h.2.2
  · intro pm x hx
    have h := pm x hx
    constructor
    · intro A B sub hA
      have ab : Sub (propRegion A) (propRegion B) := (boolean_subset_bridge A B).mp sub
      have result := h.1 (propRegion A) (propRegion B) ab
      have hA2 : fromBooleanMechanism f x (propRegion A) := by
        simpa only [fromBooleanMechanism, propOf, bool_prop_region] using hA
      simpa only [fromBooleanMechanism, propOf, bool_prop_region] using result hA2
    constructor
    · rw [← none x]
      simpa only [fromBooleanMechanism, propOf, boolean_empty_bridge] using h.2.1
    · simpa only [fromBooleanMechanism, propOf, par x] using h.2.2

noncomputable def BooleanInsert {α : Type u} (y : α) (S : BooleanRegion α) : BooleanRegion α := by
  classical
  exact fun z => if z = y then true else S z

def BooleanRelevant {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) : Prop :=
  ∀ x, C x = true → ∀ y, BooleanParents C D x y = true →
    ∃ S, (∀ z, S z = true → BooleanParents C D x z = true ∧ z ≠ y) ∧
      f x S = false ∧ f x (BooleanInsert y S) = true

theorem boolean_insert_bridge {α : Type u} (y : α) (S : BooleanRegion α) :
    propRegion (BooleanInsert y S) = (fun z => z = y ∨ propRegion S z) := by
  classical
  funext z
  apply propext
  by_cases eq : z = y <;> simp [BooleanInsert, propRegion, propOf, eq]

theorem boolean_relevance_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) :
    BooleanRelevant C D f ↔ Relevant (propRegion C) (propRelation D) (fromBooleanMechanism f) := by
  classical
  have par (x : α) : propRegion (BooleanParents C D x) = Parents (propRegion C) (propRelation D) x :=
    boolean_parents_bridge C D x
  have ins (y : α) (S : BooleanRegion α) :
      boolRegion (fun z => z = y ∨ propRegion S z) = BooleanInsert y S := by
    rw [← boolean_insert_bridge y S, bool_prop_region]
  constructor
  · intro br x hx y hy
    have hyB : BooleanParents C D x y = true := by
      have hp : propRegion (BooleanParents C D x) y := by rw [par]; exact hy
      exact hp
    obtain ⟨S, sub, neg, pos⟩ := br x hx y hyB
    refine ⟨propRegion S, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hp, hne⟩ := sub z hz
      exact ⟨by rw [← par]; exact hp, hne⟩
    · simp only [fromBooleanMechanism, propOf, bool_prop_region, neg, Bool.false_eq_true, not_false_eq_true]
    · simpa only [fromBooleanMechanism, propOf, ins] using pos
  · intro pr x hx y hy
    have hyP : Parents (propRegion C) (propRelation D) x y := by
      rw [← par]
      exact hy
    obtain ⟨S, sub, neg, pos⟩ := pr x hx y hyP
    refine ⟨boolRegion S, ?_, ?_, ?_⟩
    · intro z hz
      have hzS : S z := (propOf_boolOf _).mp hz
      obtain ⟨hp, hne⟩ := sub hzS
      refine ⟨?_, hne⟩
      have hpB : propRegion (BooleanParents C D x) z := by rw [par]; exact hp
      exact hpB
    · have hneg : ¬ f x (boolRegion S) = true := neg
      cases eq : f x (boolRegion S) <;> simp_all
    · have pos' : f x (boolRegion (fun z => z = y ∨ S z)) = true := pos
      have hs : boolRegion (fun z => z = y ∨ S z) = BooleanInsert y (boolRegion S) := by
        simpa only [prop_bool_region] using ins y (boolRegion S)
      rw [hs] at pos'
      exact pos'

noncomputable def BooleanStep {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) (U X : BooleanRegion α) : BooleanRegion α :=
  fun x => boolOf (U x = true ∨ (C x = true ∧ (∃ y, BooleanParents C D x y = true) ∧
    f x (fun y => X y && BooleanParents C D x y) = true))

theorem boolean_intersection_bridge {α : Type u} (A B : BooleanRegion α) :
    boolRegion (fun y => propRegion A y ∧ propRegion B y) = (fun y => A y && B y) := by
  funext y
  cases ha : A y <;> cases hb : B y <;> simp [boolRegion, boolOf, propRegion, propOf, ha, hb]

theorem boolean_step_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) (U X : BooleanRegion α) :
    propRegion (BooleanStep C D f U X) =
      Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U) (propRegion X) := by
  funext x
  apply propext
  have par := boolean_parents_bridge C D x
  have inp := boolean_intersection_bridge X (BooleanParents C D x)
  rw [par] at inp
  change propOf (boolOf (U x = true ∨ (C x = true ∧
    (∃ y, BooleanParents C D x y = true) ∧
    f x (fun y => X y && BooleanParents C D x y) = true))) ↔ _
  rw [propOf_boolOf]
  constructor
  · rintro (hu | ⟨hc, ⟨y, hy⟩, hf⟩)
    · exact Or.inl hu
    · refine Or.inr ⟨hc, ⟨y, ?_⟩, ?_⟩
      · rw [← par]; exact hy
      · change f x (boolRegion (fun y => propRegion X y ∧ Parents (propRegion C) (propRelation D) x y)) = true
        rw [inp]; exact hf
  · rintro (hu | ⟨hc, ⟨y, hy⟩, hf⟩)
    · exact Or.inl hu
    · refine Or.inr ⟨hc, ⟨y, ?_⟩, ?_⟩
      · have hyB : propRegion (BooleanParents C D x) y := by rw [par]; exact hy
        exact hyB
      · change f x (boolRegion (fun y => propRegion X y ∧ Parents (propRegion C) (propRelation D) x y)) = true at hf
        rw [inp] at hf
        exact hf

def BooleanLeast {α : Type u} (F : BooleanRegion α → BooleanRegion α) (x : α) : Prop :=
  ∀ S, BooleanSubset (F S) S → S x = true

def BooleanGreatest {α : Type u} (F : BooleanRegion α → BooleanRegion α) (x : α) : Prop :=
  ∃ S, BooleanSubset S (F S) ∧ S x = true

noncomputable def PropOperator {α : Type u} (F : BooleanRegion α → BooleanRegion α)
    (S : Region α) : Region α := propRegion (F (boolRegion S))

theorem boolean_least_bridge {α : Type u} (F : BooleanRegion α → BooleanRegion α) (x : α) :
    BooleanLeast F x ↔ Least (PropOperator F) x := by
  constructor
  · intro h S pre
    have bpre : BooleanSubset (F (boolRegion S)) (boolRegion S) := by
      apply (boolean_subset_bridge _ _).mpr
      simpa only [PropOperator, prop_bool_region] using pre
    have hs := h (boolRegion S) bpre
    exact (propOf_boolOf _).mp hs
  · intro h S pre
    have ppre : Sub (PropOperator F (propRegion S)) (propRegion S) := by
      have hb := (boolean_subset_bridge _ _).mp pre
      simpa only [PropOperator, bool_prop_region] using hb
    have hs := h (propRegion S) ppre
    exact hs

theorem boolean_greatest_bridge {α : Type u} (F : BooleanRegion α → BooleanRegion α) (x : α) :
    BooleanGreatest F x ↔ Greatest (PropOperator F) x := by
  constructor
  · rintro ⟨S, post, hx⟩
    refine ⟨propRegion S, ?_, hx⟩
    have hb := (boolean_subset_bridge _ _).mp post
    simpa only [PropOperator, bool_prop_region] using hb
  · rintro ⟨S, post, hx⟩
    refine ⟨boolRegion S, ?_, (propOf_boolOf _).mpr hx⟩
    apply (boolean_subset_bridge _ _).mpr
    simpa only [PropOperator, prop_bool_region] using post

theorem boolean_context_operator_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) (U : BooleanRegion α) :
    PropOperator (BooleanStep C D f U) =
      Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U) := by
  funext X
  simpa only [PropOperator, prop_bool_region] using boolean_step_bridge C D f U (boolRegion X)

def BooleanPatternRealized {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (U L Z : BooleanRegion α) : Prop :=
  ∃ f, BooleanMechanism C D f ∧ BooleanRelevant C D f ∧
    (∀ x, BooleanLeast (BooleanStep C D f U) x ↔ L x = true) ∧
    (∀ x, BooleanGreatest (BooleanStep C D f U) x ↔ C x = true ∧ Z x = false)

theorem bool_false_iff_not_true (b : Bool) : b = false ↔ ¬ b = true := by
  cases b <;> simp

theorem boolean_pattern_realization_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (U L Z Q : BooleanRegion α)
    (part : StatusPartition (propRegion C) (propRegion L) (propRegion Z) (propRegion Q))
    (ctx : Sub (propRegion U) (Roots (propRegion C) (propRelation D))) :
    BooleanPatternRealized C D U L Z ↔
      PatternConditions (propRegion C) (propRelation D) (propRegion U)
        (propRegion L) (propRegion Z) (propRegion Q) := by
  constructor
  · rintro ⟨f, adm, rel, low, high⟩
    have pa := (boolean_mechanism_bridge C D f).mp adm
    have pr := (boolean_relevance_bridge C D f).mp rel
    have op := boolean_context_operator_bridge C D f U
    have lowEq : Least (Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U)) = propRegion L := by
      funext x; apply propext
      have h := boolean_least_bridge (BooleanStep C D f U) x
      rw [op] at h
      exact h.symm.trans (low x)
    have highEq : Greatest (Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U)) =
        (fun x => propRegion C x ∧ ¬ propRegion Z x) := by
      funext x; apply propext
      have h := boolean_greatest_bridge (BooleanStep C D f U) x
      rw [op] at h
      have conv : (C x = true ∧ Z x = false) ↔ (propRegion C x ∧ ¬ propRegion Z x) := by
        constructor
        · rintro ⟨hc, hz⟩; exact ⟨hc, (bool_false_iff_not_true _).mp hz⟩
        · rintro ⟨hc, hz⟩; exact ⟨hc, (bool_false_iff_not_true _).mpr hz⟩
      exact h.symm.trans ((high x).trans conv)
    exact realized_pattern_necessary part ctx pa lowEq highEq
  · intro cond
    have result := pattern_witness_extrema part cond ctx
    let pf := StatusMechanism (propRegion C) (propRelation D) (propRegion L) (propRegion Z) (propRegion Q)
    let bf := toBooleanMechanism pf
    have pfEq : fromBooleanMechanism bf = pf := from_to_boolean_mechanism pf
    have ba : BooleanMechanism C D bf := (boolean_mechanism_bridge C D bf).mpr (by rw [pfEq]; exact result.1)
    have br : BooleanRelevant C D bf := (boolean_relevance_bridge C D bf).mpr (by rw [pfEq]; exact result.2.1)
    have op := boolean_context_operator_bridge C D bf U
    rw [pfEq] at op
    refine ⟨bf, ba, br, ?_, ?_⟩
    · intro x
      have h := boolean_least_bridge (BooleanStep C D bf U) x
      rw [op, result.2.2.1] at h
      exact h
    · intro x
      have h := boolean_greatest_bridge (BooleanStep C D bf U) x
      rw [op, result.2.2.2] at h
      have conv : (propRegion C x ∧ ¬ propRegion Z x) ↔ (C x = true ∧ Z x = false) := by
        constructor
        · rintro ⟨hc, hz⟩; exact ⟨hc, (bool_false_iff_not_true _).mpr hz⟩
        · rintro ⟨hc, hz⟩; exact ⟨hc, (bool_false_iff_not_true _).mp hz⟩
      exact h.trans conv

noncomputable def BooleanRoots {α : Type u} (C : BooleanRegion α) (D : α → α → Bool) : BooleanRegion α :=
  fun x => boolOf (C x = true ∧ ∀ y, BooleanParents C D x y = false)

theorem boolean_roots_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool) :
    propRegion (BooleanRoots C D) = Roots (propRegion C) (propRelation D) := by
  funext x
  apply propext
  change (propOf (boolOf (C x = true ∧ ∀ y, BooleanParents C D x y = false))) ↔ _
  rw [propOf_boolOf]
  constructor
  · rintro ⟨hc, hnone⟩
    refine ⟨hc, ?_⟩
    intro y hy
    have hyB : propRegion (BooleanParents C D x) y := by rw [boolean_parents_bridge]; exact hy
    simp [propRegion, propOf, hnone y] at hyB
  · rintro ⟨hc, hnone⟩
    refine ⟨hc, ?_⟩
    intro y
    have hn : ¬ propRegion (BooleanParents C D x) y := by rw [boolean_parents_bridge]; exact hnone y
    cases h : BooleanParents C D x y <;> simp_all [propRegion, propOf]

theorem boolean_legal_context_bridge {α : Type u} (C U : BooleanRegion α) (D : α → α → Bool) :
    BooleanSubset U (BooleanRoots C D) ↔ Sub (propRegion U) (Roots (propRegion C) (propRelation D)) := by
  rw [boolean_subset_bridge, boolean_roots_bridge]

def BooleanPartition {α : Type u} (C L Z Q : BooleanRegion α) : Prop :=
  (∀ x, C x = true ↔ L x = true ∨ Z x = true ∨ Q x = true) ∧
  (∀ x, ¬ (L x = true ∧ Z x = true)) ∧
  (∀ x, ¬ (L x = true ∧ Q x = true)) ∧
  (∀ x, ¬ (Z x = true ∧ Q x = true))

theorem boolean_partition_bridge {α : Type u} (C L Z Q : BooleanRegion α) :
    BooleanPartition C L Z Q ↔ StatusPartition (propRegion C) (propRegion L) (propRegion Z) (propRegion Q) := by
  rfl

theorem boolean_context_least_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) (U : BooleanRegion α) (x : α) :
    BooleanLeast (BooleanStep C D f U) x ↔
      Least (Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U)) x := by
  rw [boolean_least_bridge, boolean_context_operator_bridge]

theorem boolean_context_greatest_bridge {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (f : α → BooleanRegion α → Bool) (U : BooleanRegion α) (x : α) :
    BooleanGreatest (BooleanStep C D f U) x ↔
      Greatest (Step (propRegion C) (propRelation D) (fromBooleanMechanism f) (propRegion U)) x := by
  rw [boolean_greatest_bridge, boolean_context_operator_bridge]

theorem boolean_exact_pattern_realization {α : Type u} (C : BooleanRegion α) (D : α → α → Bool)
    (U L Z Q : BooleanRegion α) (part : BooleanPartition C L Z Q)
    (ctx : BooleanSubset U (BooleanRoots C D)) :
    BooleanPatternRealized C D U L Z ↔
      PatternConditions (propRegion C) (propRelation D) (propRegion U)
        (propRegion L) (propRegion Z) (propRegion Q) :=
  boolean_pattern_realization_bridge C D U L Z Q ((boolean_partition_bridge C L Z Q).mp part)
    ((boolean_legal_context_bridge C U D).mp ctx)

end DeterminationPatterns
