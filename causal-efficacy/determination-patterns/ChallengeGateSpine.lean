module
import Std
@[expose] public section


/-! Self-contained statement and proof surface for the relevant labelled-spine synthesis and interventions. -/
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

/-- Each carrier edge has a subset of the other parents on which its target
output is false and becomes true when that parent is added. -/
def Relevant {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ x, C x → ∀ y, Parents C D x y →
    ∃ S : Region α, Sub S (fun z => Parents C D x z ∧ z ≠ y) ∧
      ¬ f x S ∧ f x (fun z => z = y ∨ S z)

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

/-- `X` is unchanged by `F`. -/
def Fixed {α : Type u} (F : Region α → Region α) (X : Region α) : Prop := F X = X


theorem least_le {α : Type u} (F : Region α → Region α) (S : Region α)
    (h : Sub (F S) S) : Sub (Least F) S := by
  intro x hx
  exact hx S h

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

/-- Classical truth-value representation; unlike a computable decision procedure,
this encodes arbitrary propositions. -/
noncomputable def boolOf (p : Prop) : Bool := by
  classical
  exact if p then true else false

def propOf (b : Bool) : Prop := b = true

@[simp] theorem propOf_boolOf (p : Prop) : propOf (boolOf p) ↔ p := by
  classical
  simp [propOf, boolOf]

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


/-- The operator has a fixed region and every fixed region equals it. -/
def UniqueFixed {α : Type u} (F : Region α → Region α) : Prop :=
  ∃ X, Fixed F X ∧ ∀ Y, Fixed F Y → Y = X

/-- One mechanism has a unique fixed solution at every legal root context. -/
def ContextDeterminate {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) : Prop :=
  ∀ U, Sub U (Roots C D) → UniqueFixed (Step C D f U)


end DeterminationPatterns

namespace DeterminationPatterns
universe u

/-- OR if the gate bit is true, AND if it is false. -/
def SpineGate (g b : Bool) (z : Prop) : Prop :=
  if g then (b = true ∨ z) else (b = true ∧ z)

theorem spine_gate_forcing (g b : Bool) (z : Prop) :
    SpineGate g b z ↔ if g = b then g = true else z := by
  cases g <;> cases b <;> simp [SpineGate]

/-- Each link satisfies its AND/OR equation for the given source assignment. -/
def SpineSolution {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (v : Region Nat) : Prop :=
  ∀ n, v n ↔ SpineGate (g n) (u (l n)) (v (n+1))

/-- Every tail contains a link whose source value agrees with its gate bit,
forcing that link independently of its successor. -/
def CofinalForcing {α : Type u} (l : Nat → α) (g : Nat → Bool) (u : α → Bool) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ g n = u (l n)

def SpineLinkStep {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (v : Region Nat) : Region Nat :=
  fun n => SpineGate (g n) (u (l n)) (v (n+1))

theorem spine_link_monotone {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) : Monotone (SpineLinkStep l g u) := by
  intro A B hAB n hn
  cases h : g n with
  | false =>
    simp only [SpineLinkStep, SpineGate, h, Bool.false_eq_true, ↓reduceIte] at hn ⊢
    exact ⟨hn.1, hAB hn.2⟩
  | true =>
    simp only [SpineLinkStep, SpineGate, h, ↓reduceIte] at hn ⊢
    exact hn.elim Or.inl (fun h => Or.inr (hAB h))

theorem spine_solution_iff_fixed {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (v : Region Nat) : SpineSolution l g u v ↔ Fixed (SpineLinkStep l g u) v := by
  constructor
  · intro h
    funext n
    exact propext (h n).symm
  · intro h n
    exact (Iff.of_eq (congrFun h n)).symm

theorem spine_solution_exists {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) : ∃ v, SpineSolution l g u v := by
  refine ⟨Least (SpineLinkStep l g u), ?_⟩
  exact (spine_solution_iff_fixed l g u _).mpr (least_fixed (spine_link_monotone l g u))

theorem spine_agreement_descends {α : Type u} {l : Nat → α} {g : Nat → Bool}
    {u : α → Bool} {v w : Region Nat} (hv : SpineSolution l g u v)
    (hw : SpineSolution l g u w) :
    ∀ k n, (v (n+k) ↔ w (n+k)) → (v n ↔ w n) := by
  intro k
  induction k with
  | zero => intro n h; simpa using h
  | succ k ih =>
    intro n h
    have next : v (n+1) ↔ w (n+1) := by
      apply ih (n+1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have gate : SpineGate (g n) (u (l n)) (v (n+1)) ↔
        SpineGate (g n) (u (l n)) (w (n+1)) := by rw [propext next]
    exact (hv n).trans (gate.trans (hw n).symm)

theorem spine_cofinal_forcing_unique {α : Type u} {l : Nat → α} {g : Nat → Bool}
    {u : α → Bool} (force : CofinalForcing l g u) :
    ∃ v, SpineSolution l g u v ∧ ∀ w, SpineSolution l g u w → w = v := by
  obtain ⟨v, hv⟩ := spine_solution_exists l g u
  refine ⟨v, hv, ?_⟩
  intro w hw
  funext n
  apply propext
  obtain ⟨m, hnm, hm⟩ := force n
  have atM : w m ↔ v m := by
    have wv := (hw m).trans (spine_gate_forcing (g m) (u (l m)) (w (m+1)))
    have vv := (hv m).trans (spine_gate_forcing (g m) (u (l m)) (v (m+1)))
    simp only [hm, ↓reduceIte] at wv vv
    exact wv.trans vv.symm
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
  rw [hk] at atM
  exact spine_agreement_descends hw hv k n atM

def SpinePrefixValue {α : Type u} (l : Nat → α) (g : Nat → Bool) (u : α → Bool)
    (b : Prop) : Nat → Nat → Prop
  | 0, _ => b
  | k+1, n => SpineGate (g n) (u (l n)) (SpinePrefixValue l g u b k (n+1))

def SpineTailValue {α : Type u} (l : Nat → α) (g : Nat → Bool) (u : α → Bool)
    (N : Nat) (b : Prop) (n : Nat) : Prop := SpinePrefixValue l g u b (N-n) n

theorem spine_tail_solution {α : Type u} {l : Nat → α} {g : Nat → Bool}
    {u : α → Bool} {N : Nat} (tail : ∀ n, N ≤ n → g n ≠ u (l n)) (b : Prop) :
    SpineSolution l g u (SpineTailValue l g u N b) := by
  intro n
  by_cases hn : n < N
  · have eq : N-n = (N-(n+1))+1 := by omega
    simp only [SpineTailValue, eq, SpinePrefixValue]
  · have eq1 : N-n = 0 := by omega
    have eq2 : N-(n+1) = 0 := by omega
    have neq : g n ≠ u (l n) := tail n (by omega)
    simp only [SpineTailValue, eq1, eq2, SpinePrefixValue]
    simpa [neq] using (spine_gate_forcing (g n) (u (l n)) b).symm

/-- A fixed gate family has one solution at a source assignment exactly when
the forced positions meet every tail. -/
theorem spine_unique_iff_cofinal_forcing {α : Type u} (l : Nat → α)
    (g : Nat → Bool) (u : α → Bool) :
    (∃ v, SpineSolution l g u v ∧ ∀ w, SpineSolution l g u w → w = v) ↔ CofinalForcing l g u := by
  classical
  constructor
  · rintro ⟨v, hv, unique⟩
    apply Classical.byContradiction
    intro notForce
    have tail : ∃ N, ∀ n, N ≤ n → g n ≠ u (l n) := by
      apply Classical.byContradiction
      intro noTail
      apply notForce
      intro N
      apply Classical.byContradiction
      intro noForce
      apply noTail
      refine ⟨N, ?_⟩
      intro n hn eq
      exact noForce ⟨n, hn, eq⟩
    obtain ⟨N, htail⟩ := tail
    have hTrue := spine_tail_solution htail True
    have hFalse := spine_tail_solution htail False
    have eq : SpineTailValue l g u N True = SpineTailValue l g u N False :=
      (unique _ hTrue).trans (unique _ hFalse).symm
    have eqN := congrFun eq N
    simp only [SpineTailValue, Nat.sub_self, SpinePrefixValue] at eqN
    exact Eq.mp eqN True.intro
  · exact spine_cofinal_forcing_unique

/-- Every tail contains two positions with the same label and opposite
gate bits; the repeated label may vary between tails. -/
def OppositeRepeats {α : Type u} (l : Nat → α) (g : Nat → Bool) : Prop :=
  ∀ N, ∃ i, N ≤ i ∧ ∃ j, N ≤ j ∧ l i = l j ∧ g i ≠ g j

/-- Every tail contains distinct positions with the same label; the label
may vary between tails. -/
def RepeatedInEveryTail {α : Type u} (l : Nat → α) : Prop :=
  ∀ N, ∃ i, N ≤ i ∧ ∃ j, N ≤ j ∧ i ≠ j ∧ l i = l j

/-- A fixed gate family has a unique solution at every source assignment
exactly when every tail has a same-label opposite-gate pair. -/
theorem all_contexts_unique_iff_opposite_repeats {α : Type u} (l : Nat → α) (g : Nat → Bool) :
    (∀ u, ∃ v, SpineSolution l g u v ∧ ∀ w, SpineSolution l g u w → w = v) ↔
      OppositeRepeats l g := by
  classical
  constructor
  · intro all
    apply Classical.byContradiction
    intro notOpp
    have tail : ∃ N, ∀ i j, N ≤ i → N ≤ j → l i = l j → g i = g j := by
      apply Classical.byContradiction
      intro noTail
      apply notOpp
      intro N
      apply Classical.byContradiction
      intro noPair
      apply noTail
      refine ⟨N, ?_⟩
      intro i j hi hj labels
      apply Classical.byContradiction
      intro diff
      exact noPair ⟨i, hi, j, hj, labels, diff⟩
    obtain ⟨N, same⟩ := tail
    clear notOpp
    let u : α → Bool := fun b => boolOf (∃ i, N ≤ i ∧ l i = b ∧ g i = false)
    have forcing := (spine_unique_iff_cofinal_forcing l g u).mp (all u)
    clear all
    have unequal : ∀ n, N ≤ n → g n ≠ u (l n) := by
      intro n hn
      cases gn : g n with
      | false =>
        have yes : ∃ i, N ≤ i ∧ l i = l n ∧ g i = false := ⟨n, hn, rfl, gn⟩
        have ut : u (l n) = true := (propOf_boolOf _).mpr yes
        simp [ut]
      | true =>
        have no : ¬ ∃ i, N ≤ i ∧ l i = l n ∧ g i = false := by
          rintro ⟨i, hi, labels, gi⟩
          have eq := same i n hi hn labels
          rw [gi, gn] at eq
          cases eq
        have uf : u (l n) = false := by simp [u, boolOf, no]
        simp [uf]
    obtain ⟨n, hn, eq⟩ := forcing N
    exact unequal n hn eq
  · intro opp u
    apply spine_cofinal_forcing_unique
    intro N
    obtain ⟨i, hi, j, hj, labels, diff⟩ := opp N
    have either : g i = u (l i) ∨ g j = u (l j) := by
      rw [← labels]
      cases hgi : g i <;> cases hgj : g j <;> cases hu : u (l i) <;> simp_all
    rcases either with ei | ej
    · exact ⟨i, hi, ei⟩
    · exact ⟨j, hj, ej⟩

/-- Parity of prior occurrences of b before position n. -/
noncomputable def OccurrenceParity {α : Type u} (l : Nat → α) (b : α) (n : Nat) : Bool := by
  classical
  exact Nat.rec false (fun k acc => if l k = b then !acc else acc) n

noncomputable def OccurrenceGate {α : Type u} (l : Nat → α) (n : Nat) : Bool :=
  OccurrenceParity l (l n) n

theorem parity_constant_on_gap {α : Type u} (l : Nat → α) (b : α) (i j : Nat) :
    i ≤ j → (∀ k, i ≤ k → k < j → l k ≠ b) → OccurrenceParity l b j = OccurrenceParity l b i := by
  classical
  induction j with
  | zero =>
    intro h _
    have eq : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    intro hij gap
    by_cases eq : i = j+1
    · rw [eq]
    · have le : i ≤ j := by omega
      have neq : l j ≠ b := gap j (by omega) (by omega)
      have prev := ih le (fun k hk hk' => gap k hk (by omega))
      simpa [OccurrenceParity, neq] using prev

theorem consecutive_occurrences_opposite {α : Type u} (l : Nat → α) {i j : Nat}
    (ij : i < j) (labels : l j = l i)
    (gap : ∀ k, i < k → k < j → l k ≠ l i) : OccurrenceGate l i ≠ OccurrenceGate l j := by
  classical
  have p : OccurrenceParity l (l i) j = OccurrenceParity l (l i) (i+1) :=
    parity_constant_on_gap l (l i) (i+1) j (by omega) (fun k hk hk' => gap k (by omega) hk')
  have flip : OccurrenceParity l (l i) (i+1) = !OccurrenceParity l (l i) i := by
    simp [OccurrenceParity]
  have gJ : OccurrenceGate l j = !OccurrenceGate l i := by
    unfold OccurrenceGate
    rw [labels, p, flip]
  rw [gJ]
  cases h : OccurrenceGate l i <;> simp

theorem repeated_tail_occurrence_gate {α : Type u} {l : Nat → α}
    (rep : RepeatedInEveryTail l) : OppositeRepeats l (OccurrenceGate l) := by
  intro N
  obtain ⟨i, hi, j, hj, ne, eq⟩ := rep N
  have pairs : ∃ i j, N ≤ i ∧ i < j ∧ l j = l i := by
    by_cases h : i < j
    · exact ⟨i, j, hi, h, eq.symm⟩
    · exact ⟨j, i, hj, by omega, eq⟩
  obtain ⟨i, j, hi, hij, lab⟩ := pairs
  have ex : ∃ k, i < k ∧ l k = l i := ⟨j, hij, lab⟩
  obtain ⟨k, ⟨hik, klab⟩, minimal⟩ := exists_min_nat (fun k => i < k ∧ l k = l i) ex
  have gap : ∀ t, i < t → t < k → l t ≠ l i := by
    intro t hit htk eq
    exact minimal t htk ⟨hit, eq⟩
  exact ⟨i, hi, k, by omega, klab.symm, consecutive_occurrences_opposite l hik klab gap⟩

/-- One fixed AND/OR family works at every source assignment exactly when
every tail contains a repeated source label. -/
theorem gate_synthesis_iff_repeated_sources {α : Type u} (l : Nat → α) :
    (∃ g, ∀ u, ∃ v, SpineSolution l g u v ∧ ∀ w, SpineSolution l g u w → w = v) ↔
      RepeatedInEveryTail l := by
  constructor
  · rintro ⟨g, h⟩ N
    have opp := (all_contexts_unique_iff_opposite_repeats l g).mp h
    obtain ⟨i, hi, j, hj, lab, diff⟩ := opp N
    have ne : i ≠ j := by intro eq; subst i; exact diff rfl
    exact ⟨i, hi, j, hj, ne, lab⟩
  · intro rep
    exact ⟨OccurrenceGate l, (all_contexts_unique_iff_opposite_repeats l _).mpr
      (repeated_tail_occurrence_gate rep)⟩

/-- The carrier has a root for every label and a link for every natural number. -/
inductive LabelNode (α : Type u) where
  | root : α → LabelNode α
  | link : Nat → LabelNode α

/-- Each link has its labelled root and next link as parents; roots have none. -/
def LabelDependency {α : Type u} (l : Nat → α) (y x : LabelNode α) : Prop :=
  match x with
  | .root _ => False
  | .link n => y = .root (l n) ∨ y = .link (n+1)

/-- OR for a true gate bit and AND for a false gate bit. -/
def PropGate (g : Bool) (b z : Prop) : Prop := if g then b ∨ z else b ∧ z

/-- The chosen AND/OR rule reads the labelled root and successor link. -/
def LabelGateMechanism {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (x : LabelNode α) (S : Region (LabelNode α)) : Prop :=
  match x with
  | .root _ => True
  | .link n => PropGate (g n) (S (.root (l n))) (S (.link (n+1)))

/-- Combine source and link assignments on the full labelled carrier. -/
def LabelState {α : Type u} (u : α → Bool) (v : Region Nat) : Region (LabelNode α) :=
  fun x => match x with
  | .root b => u b = true
  | .link n => v n

/-- The active roots prescribed by a source assignment; links are excluded. -/
def LabelContext {α : Type u} (u : α → Bool) : Region (LabelNode α) :=
  fun x => match x with
  | .root b => u b = true
  | .link _ => False

theorem label_gate_admissible {α : Type u} (l : Nat → α) (g : Nat → Bool) :
    Mechanism (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) := by
  intro x _
  cases x with
  | root b => simp [LabelGateMechanism, Parents, LabelDependency]
  | link n =>
    cases hg : g n with
    | false =>
      simp only [LabelGateMechanism, PropGate, hg, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro A B sub h; exact ⟨sub h.1, sub h.2⟩
      constructor
      · constructor
        · intro h; exact False.elim h.1
        · intro h; exact False.elim (h (.root (l n)) ⟨True.intro, Or.inl rfl⟩)
      · exact ⟨⟨True.intro, Or.inl rfl⟩, ⟨True.intro, Or.inr rfl⟩⟩
    | true =>
      simp only [LabelGateMechanism, PropGate, hg, ↓reduceIte]
      constructor
      · intro A B sub h; exact h.elim (fun a => Or.inl (sub a)) (fun b => Or.inr (sub b))
      constructor
      · constructor
        · intro h; exact h.elim (fun x => False.elim x) (fun x => False.elim x)
        · intro h; exact False.elim (h (.root (l n)) ⟨True.intro, Or.inl rfl⟩)
      · exact Or.inl ⟨True.intro, Or.inl rfl⟩

theorem label_gate_relevant {α : Type u} (l : Nat → α) (g : Nat → Bool) :
    Relevant (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) := by
  intro x _ y hy
  cases x with
  | root b => exact False.elim hy.2
  | link n =>
    rcases hy.2 with eq | eq
    · subst y
      cases hg : g n with
      | false =>
        refine ⟨(fun z => z = .link (n+1)), ?_, ?_, ?_⟩
        · intro z hz; subst z; simp [Parents, LabelDependency]
        · simp [LabelGateMechanism, PropGate, hg]
        · simp [LabelGateMechanism, PropGate, hg]
      | true =>
        refine ⟨(fun _ => False), ?_, ?_, ?_⟩
        · intro z hz; exact False.elim hz
        · simp [LabelGateMechanism, PropGate, hg]
        · simp [LabelGateMechanism, PropGate, hg]
    · subst y
      cases hg : g n with
      | false =>
        refine ⟨(fun z => z = .root (l n)), ?_, ?_, ?_⟩
        · intro z hz; subst z; simp [Parents, LabelDependency]
        · simp [LabelGateMechanism, PropGate, hg]
        · simp [LabelGateMechanism, PropGate, hg]
      | true =>
        refine ⟨(fun _ => False), ?_, ?_, ?_⟩
        · intro z hz; exact False.elim hz
        · simp [LabelGateMechanism, PropGate, hg]
        · simp [LabelGateMechanism, PropGate, hg]

@[simp] theorem label_step_root {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (X : Region (LabelNode α)) (b : α) :
    Step (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) (LabelContext u) X (.root b) ↔ u b = true := by
  simp [Step, LabelContext, Parents, LabelDependency]

@[simp] theorem label_step_link {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (X : Region (LabelNode α)) (n : Nat) :
    Step (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) (LabelContext u) X (.link n) ↔
      PropGate (g n) (X (.root (l n))) (X (.link (n+1))) := by
  simp [Step, LabelContext, Parents, LabelDependency, LabelGateMechanism]

theorem label_state_fixed_iff {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (v : Region Nat) :
    Fixed (Step (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) (LabelContext u))
      (LabelState u v) ↔ SpineSolution l g u v := by
  constructor
  · intro fixed n
    have h := (Iff.of_eq (congrFun fixed (.link n))).symm
    simpa [LabelState, SpineGate, PropGate] using h
  · intro sol
    funext x
    apply propext
    cases x with
    | root b => simp [LabelState]
    | link n =>
      have h := sol n
      simpa [LabelState, SpineGate, PropGate] using h.symm

theorem label_context_legal {α : Type u} (l : Nat → α) (u : α → Bool) :
    Sub (LabelContext u) (Roots (fun _ => True) (LabelDependency l)) := by
  intro x h
  cases x with
  | root b => simp [Roots, Parents, LabelDependency]
  | link n => exact False.elim h

theorem legal_label_context {α : Type u} (l : Nat → α) (U : Region (LabelNode α))
    (ctx : Sub U (Roots (fun _ => True) (LabelDependency l))) :
    U = LabelContext (fun b => boolOf (U (.root b))) := by
  funext x
  apply propext
  cases x with
  | root b => exact (propOf_boolOf _).symm
  | link n =>
    constructor
    · intro h
      exact (ctx h).2 (.root (l n)) ⟨True.intro, Or.inl rfl⟩
    · intro h; exact False.elim h

theorem labelled_state_injective {α : Type u} (u : α → Bool) (v w : Region Nat) :
    LabelState u v = LabelState u w → v = w := by
  intro h
  funext n
  exact congrFun h (.link n)

theorem label_fixed_as_state {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (X : Region (LabelNode α))
    (fixed : Fixed (Step (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) (LabelContext u)) X) :
    X = LabelState u (fun n => X (.link n)) := by
  funext x
  apply propext
  cases x with
  | root b =>
    exact (Iff.of_eq (congrFun fixed (.root b))).symm.trans (label_step_root l g u X b)
  | link n => exact Iff.rfl

theorem labelled_context_determinate_iff {α : Type u} (l : Nat → α) (g : Nat → Bool) :
    ContextDeterminate (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) ↔
      ∀ u, ∃ v, SpineSolution l g u v ∧ ∀ w, SpineSolution l g u w → w = v := by
  constructor
  · intro det u
    obtain ⟨X, fx, unique⟩ := det (LabelContext u) (label_context_legal l u)
    clear det
    let v : Region Nat := fun n => X (.link n)
    have state := label_fixed_as_state l g u X fx
    have sol : SpineSolution l g u v := by
      apply (label_state_fixed_iff l g u v).mp
      rw [← state]
      exact fx
    refine ⟨v, sol, ?_⟩
    intro w hw
    have fw := (label_state_fixed_iff l g u w).mpr hw
    have eq : LabelState u w = LabelState u v := (unique _ fw).trans state
    exact labelled_state_injective u w v eq
  · intro all U ctx
    rw [legal_label_context l U ctx]
    clear ctx
    let u := fun b => boolOf (U (.root b))
    obtain ⟨v, sol, unique⟩ := all u
    clear all
    refine ⟨LabelState u v, (label_state_fixed_iff l g u v).mpr sol, ?_⟩
    intro X fx
    let w : Region Nat := fun n => X (.link n)
    have state := label_fixed_as_state l g u X fx
    have ws : SpineSolution l g u w := by
      apply (label_state_fixed_iff l g u w).mp
      rw [← state]
      exact fx
    rw [state]
    change LabelState u w = LabelState u v
    rw [unique w ws]

theorem subset_singleton_cases {β : Type u} (S : Region β) (q : β)
    (h : Sub S (fun z => z = q)) : S = (fun _ => False) ∨ S = (fun z => z = q) := by
  classical
  by_cases sq : S q
  · right
    funext z
    apply propext
    constructor
    · intro hz; exact h hz
    · intro eq; subst z; exact sq
  · left
    funext z
    apply propext
    constructor
    · intro hz
      have eq := h hz
      subst z
      exact sq hz
    · intro hz; exact False.elim hz

theorem two_relevant_singletons_agree {β : Type u} (p q : β) (f : Region β → Prop)
    (_neq : p ≠ q)
    (rp : ∃ S, Sub S (fun z => (z = p ∨ z = q) ∧ z ≠ p) ∧
      ¬ f S ∧ f (fun z => z = p ∨ S z))
    (rq : ∃ S, Sub S (fun z => (z = p ∨ z = q) ∧ z ≠ q) ∧
      ¬ f S ∧ f (fun z => z = q ∨ S z)) :
    f (fun z => z = p) ↔ f (fun z => z = q) := by
  classical
  clear _neq
  obtain ⟨Sp, hSp, np, pp⟩ := rp
  obtain ⟨Sq, hSq, nq, pq⟩ := rq
  have psub : Sub Sp (fun z => z = q) := by
    intro z hz
    rcases (hSp hz).1 with hzP | hzQ
    · exact False.elim ((hSp hz).2 hzP)
    · exact hzQ
  clear hSp
  have qsub : Sub Sq (fun z => z = p) := by
    intro z hz
    rcases (hSq hz).1 with hzP | hzQ
    · exact hzP
    · exact False.elim ((hSq hz).2 hzQ)
  clear hSq
  have cp := subset_singleton_cases Sp q psub
  have cq := subset_singleton_cases Sq p qsub
  clear psub qsub
  constructor
  · clear cp np pp Sp
    intro fp
    rcases cq with empty | single
    · subst Sq
      simpa using pq
    · subst Sq
      exact False.elim (nq fp)
  · clear cq nq pq Sq
    intro fq
    rcases cp with empty | single
    · subst Sp
      simpa using pp
    · subst Sp
      exact False.elim (np fq)

theorem two_relevant_inputs_classify {β : Type u} (p q : β) (f : Region β → Prop)
    (neq : p ≠ q) (zero : ¬ f (fun _ => False)) (one : f (fun z => z = p ∨ z = q))
    (rp : ∃ S, Sub S (fun z => (z = p ∨ z = q) ∧ z ≠ p) ∧
      ¬ f S ∧ f (fun z => z = p ∨ S z))
    (rq : ∃ S, Sub S (fun z => (z = p ∨ z = q) ∧ z ≠ q) ∧
      ¬ f S ∧ f (fun z => z = q ∨ S z)) (X : Region β) :
    f (fun z => X z ∧ (z = p ∨ z = q)) ↔
      PropGate (boolOf (f (fun z => z = p))) (X p) (X q) := by
  classical
  have singles := two_relevant_singletons_agree p q f neq rp rq
  clear neq rp rq
  by_cases hp : X p <;> by_cases hq : X q
  · clear singles zero
    have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = p ∨ z = q) := by
      funext z; apply propext
      constructor
      · intro h; exact h.2
      · intro h; rcases h with rfl | rfl <;> simp [hp, hq]
    rw [eq]
    by_cases hf : f (fun z => z = p) <;> simp [PropGate, boolOf, hf, hp, hq, one]
  · clear singles zero one
    have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = p) := by
      funext z; apply propext
      constructor
      · rintro ⟨_, hz | hz⟩
        · exact hz
        · subst z; exact False.elim (hq ‹X q›)
      · intro hz; subst z; exact ⟨hp, Or.inl rfl⟩
    rw [eq]
    by_cases hf : f (fun z => z = p) <;> simp [PropGate, boolOf, hf, hp, hq]
  · clear zero one
    have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = q) := by
      funext z; apply propext
      constructor
      · rintro ⟨_, hz | hz⟩
        · subst z; exact False.elim (hp ‹X p›)
        · exact hz
      · intro hz; subst z; exact ⟨hq, Or.inr rfl⟩
    rw [eq]
    by_cases hf : f (fun z => z = p)
    · have hqf := singles.mp hf
      simp [PropGate, boolOf, hf, hp, hq, hqf]
    · have hqf : ¬ f (fun z => z = q) := fun h => hf (singles.mpr h)
      simp [PropGate, boolOf, hf, hp, hq, hqf]
  · clear singles one
    have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun _ => False) := by
      funext z; apply propext
      constructor
      · rintro ⟨hzX, hz | hz⟩
        · subst z; exact hp hzX
        · subst z; exact hq hzX
      · intro h; exact False.elim h
    rw [eq]
    by_cases hf : f (fun z => z = p) <;> simp [PropGate, boolOf, hf, hp, hq, zero]

noncomputable def ExtractGate {α : Type u} (l : Nat → α)
    (f : LabelNode α → Region (LabelNode α) → Prop) (n : Nat) : Bool :=
  boolOf (f (.link n) (fun z => z = .root (l n)))

theorem relevant_mechanism_gate_reduction {α : Type u} (l : Nat → α)
    (f : LabelNode α → Region (LabelNode α) → Prop)
    (adm : Mechanism (fun _ => True) (LabelDependency l) f)
    (rel : Relevant (fun _ => True) (LabelDependency l) f)
    (n : Nat) (X : Region (LabelNode α)) :
    f (.link n) (fun y => X y ∧ Parents (fun _ => True) (LabelDependency l) (.link n) y) ↔
      PropGate (ExtractGate l f n) (X (.root (l n))) (X (.link (n+1))) := by
  let p : LabelNode α := .root (l n)
  let q : LabelNode α := .link (n+1)
  have neq : p ≠ q := by
    change LabelNode.root (l n) ≠ LabelNode.link (n+1)
    intro eq; cases eq
  have parents : Parents (fun _ => True) (LabelDependency l) (.link n) = (fun z => z = p ∨ z = q) := by
    funext z
    apply propext
    simp [Parents, LabelDependency, p, q]
  have zero : ¬ f (.link n) (fun _ => False) := by
    intro h
    have none := ((adm (.link n) True.intro).2.1).mp h
    exact none p ⟨True.intro, Or.inl rfl⟩
  have one : f (.link n) (fun z => z = p ∨ z = q) := by
    rw [← parents]
    exact (adm (.link n) True.intro).2.2
  have rp := rel (.link n) True.intro p ⟨True.intro, Or.inl rfl⟩
  have rq := rel (.link n) True.intro q ⟨True.intro, Or.inr rfl⟩
  rw [parents] at rp rq
  rw [parents]
  exact two_relevant_inputs_classify p q (f (.link n)) neq zero one rp rq X

theorem relevant_context_operator_reduction {α : Type u} (l : Nat → α)
    (f : LabelNode α → Region (LabelNode α) → Prop)
    (adm : Mechanism (fun _ => True) (LabelDependency l) f)
    (rel : Relevant (fun _ => True) (LabelDependency l) f) (U : Region (LabelNode α)) :
    Step (fun _ => True) (LabelDependency l) f U =
      Step (fun _ => True) (LabelDependency l) (LabelGateMechanism l (ExtractGate l f)) U := by
  funext X x
  apply propext
  cases x with
  | root b => simp [Step, Parents, LabelDependency]
  | link n =>
    have eq := relevant_mechanism_gate_reduction l f adm rel n X
    clear adm rel
    have gateEq : PropGate (ExtractGate l f n)
        (X (.root (l n)) ∧ Parents (fun _ => True) (LabelDependency l) (.link n) (.root (l n)))
        (X (.link (n+1)) ∧ Parents (fun _ => True) (LabelDependency l) (.link n) (.link (n+1))) ↔
        PropGate (ExtractGate l f n) (X (.root (l n))) (X (.link (n+1))) := by
      simp [Parents, LabelDependency]
    simp only [Step, LabelGateMechanism]
    constructor
    · rintro (hu | ⟨hc, hp, hf⟩)
      · exact Or.inl hu
      · exact Or.inr ⟨hc, hp, gateEq.mpr (eq.mp hf)⟩
    · rintro (hu | ⟨hc, hp, hg⟩)
      · exact Or.inl hu
      · exact Or.inr ⟨hc, hp, eq.mpr (gateEq.mp hg)⟩

/-- A single admissible, fully edge-relevant mechanism has a unique solution
at every legal context exactly when each tail repeats a source label. -/
theorem relevant_labelled_spine_synthesis_iff {α : Type u} (l : Nat → α) :
    (∃ f, Mechanism (fun _ => True) (LabelDependency l) f ∧
      Relevant (fun _ => True) (LabelDependency l) f ∧
      ContextDeterminate (fun _ => True) (LabelDependency l) f) ↔ RepeatedInEveryTail l := by
  constructor
  · rintro ⟨f, adm, rel, det⟩
    let g := ExtractGate l f
    have detGate : ContextDeterminate (fun _ => True) (LabelDependency l) (LabelGateMechanism l g) := by
      intro U ctx
      have eq := relevant_context_operator_reduction l f adm rel U
      have h := det U ctx
      rw [eq] at h
      exact h
    apply (gate_synthesis_iff_repeated_sources l).mp
    exact ⟨g, (labelled_context_determinate_iff l g).mp detGate⟩
  · intro rep
    obtain ⟨g, all⟩ := (gate_synthesis_iff_repeated_sources l).mpr rep
    exact ⟨LabelGateMechanism l g, label_gate_admissible l g, label_gate_relevant l g,
      (labelled_context_determinate_iff l g).mpr all⟩

/-- Link assignments satisfy prescribed values on `I` and the original gate
equations outside `I`; `I` may be infinite. -/
noncomputable def IntervenedSpineSolution {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (I : Region Nat) (w : Nat → Bool) (v : Region Nat) : Prop := by
  classical
  exact ∀ n, v n ↔ if I n then w n = true else SpineGate (g n) (u (l n)) (v (n+1))

/-- At intervened links use the prescribed value as the forcing gate bit. -/
noncomputable def IntervenedGate (g : Nat → Bool) (I : Region Nat) (w : Nat → Bool) : Nat → Bool := by
  classical
  exact fun n => if I n then w n else g n

/-- At intervened links use the prescribed value; elsewhere use the source. -/
noncomputable def IntervenedContext {α : Type u} (l : Nat → α) (u : α → Bool)
    (I : Region Nat) (w : Nat → Bool) : Nat → Bool := by
  classical
  exact fun n => if I n then w n else u (l n)

theorem intervention_as_forced_links {α : Type u} (l : Nat → α) (g : Nat → Bool)
    (u : α → Bool) (I : Region Nat) (w : Nat → Bool) (v : Region Nat) :
    IntervenedSpineSolution l g u I w v ↔
      SpineSolution (fun n => n) (IntervenedGate g I w) (IntervenedContext l u I w) v := by
  classical
  unfold IntervenedSpineSolution SpineSolution
  apply forall_congr'
  intro n
  by_cases hi : I n
  · simp only [hi, ↓reduceIte, IntervenedGate, IntervenedContext]
    have h := spine_gate_forcing (w n) (w n) (v (n+1))
    simp only [↓reduceIte] at h
    rw [propext h]
  · simp [IntervenedGate, IntervenedContext, hi]

theorem forcing_survives_intervention {α : Type u} {l : Nat → α} {g : Nat → Bool}
    {u : α → Bool} (force : CofinalForcing l g u) (I : Region Nat) (w : Nat → Bool) :
    CofinalForcing (fun n => n) (IntervenedGate g I w) (IntervenedContext l u I w) := by
  classical
  intro N
  obtain ⟨n, hn, eq⟩ := force N
  refine ⟨n, hn, ?_⟩
  by_cases hi : I n
  · simp [IntervenedGate, IntervenedContext, hi]
  · simpa [IntervenedGate, IntervenedContext, hi] using eq

/-- A gate family with opposite repeated gates in every tail remains unique
under any hard intervention on original links and any source assignment. -/
theorem relevant_synthesis_survives_all_hard_interventions {α : Type u} {l : Nat → α}
    {g : Nat → Bool} (opp : OppositeRepeats l g) (u : α → Bool) (I : Region Nat) (w : Nat → Bool) :
    ∃ v, IntervenedSpineSolution l g u I w v ∧
      ∀ z, IntervenedSpineSolution l g u I w z → z = v := by
  have all := (all_contexts_unique_iff_opposite_repeats l g).mpr opp
  have force := (spine_unique_iff_cofinal_forcing l g u).mp (all u)
  obtain ⟨v, hv, unique⟩ := spine_cofinal_forcing_unique (forcing_survives_intervention force I w)
  refine ⟨v, (intervention_as_forced_links l g u I w v).mpr hv, ?_⟩
  intro z hz
  exact unique z ((intervention_as_forced_links l g u I w z).mp hz)

end DeterminationPatterns
