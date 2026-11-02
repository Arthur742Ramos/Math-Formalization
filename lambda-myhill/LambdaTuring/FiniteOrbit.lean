/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.MyhillFibers
public meta import LambdaTuring.MyhillFibers

@[expose] public section

namespace LambdaTuring

/-- Follow a partial successor map; once no successor exists the orbit stops. -/
def partialOrbit (step : Nat → Option Nat) (root : Nat) : Nat → Option Nat
  | 0 => some root
  | n + 1 => (partialOrbit step root n).bind step

theorem partialOrbit_succ_some (step : Nat → Option Nat) (root n x : Nat)
    (h : partialOrbit step root (n + 1) = some x) :
    ∃ y, partialOrbit step root n = some y ∧ step y = some x := by
  cases hp : partialOrbit step root n with
  | none => simp [partialOrbit, hp] at h
  | some y =>
    refine ⟨y, rfl, ?_⟩
    simpa [partialOrbit, hp] using h

/-- Before termination, an injective partial successor cannot revisit a
point when the root has no predecessor. -/
theorem partialOrbit_no_repeats (step : Nat → Option Nat) (root : Nat)
    (hinj : ∀ a b x, step a = some x → step b = some x → a = b)
    (hroot : ∀ a, step a ≠ some root) :
    ∀ i j x, partialOrbit step root i = some x → partialOrbit step root j = some x → i = j := by
  intro i
  induction i with
  | zero =>
    intro j x hi hj
    have hx : x = root := by simpa [partialOrbit] using hi.symm
    subst x
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨a, _, ha⟩ := partialOrbit_succ_some step root j root hj
      exact False.elim (hroot a ha)
  | succ i ih =>
    intro j x hi hj
    cases j with
    | zero =>
      have hx : x = root := by simpa [partialOrbit] using hj.symm
      subst x
      obtain ⟨a, _, ha⟩ := partialOrbit_succ_some step root i root hi
      exact False.elim (hroot a ha)
    | succ j =>
      obtain ⟨a, ha, hax⟩ := partialOrbit_succ_some step root i x hi
      obtain ⟨b, hb, hbx⟩ := partialOrbit_succ_some step root j x hj
      have hab : a = b := hinj a b x hax hbx
      subst b
      exact congrArg Nat.succ (ih j a ha hb)

/-- An injective partial path whose successful values lie in a finite list
must terminate when it starts outside that list. -/
theorem partialOrbit_terminates (step : Nat → Option Nat) (root : Nat) (support : List Nat)
    (hinj : ∀ a b x, step a = some x → step b = some x → a = b)
    (hsupport : ∀ a x, step a = some x → x ∈ support)
    (hroot : root ∉ support) : ∃ n, partialOrbit step root n = none := by
  by_contra hnone
  have hex (n : Nat) : ∃ x, partialOrbit step root n = some x := by
    apply Option.ne_none_iff_exists'.1
    intro hn
    exact hnone ⟨n, hn⟩
  have hroot' : ∀ a, step a ≠ some root := by
    intro a ha
    exact hroot (hsupport a root ha)
  let value : Nat → Nat := fun n => (partialOrbit step root (n + 1)).getD root
  have hv : Function.Injective value := by
    intro i j hij
    obtain ⟨x, hx⟩ := hex (i + 1)
    obtain ⟨y, hy⟩ := hex (j + 1)
    have hxy : x = y := by simpa [value, hx, hy] using hij
    subst y
    have he := partialOrbit_no_repeats step root hinj hroot' (i + 1) (j + 1) x hx hy
    omega
  obtain ⟨k, _, hk⟩ := injective_outside_prefix value hv support
  obtain ⟨x, hx⟩ := hex (k + 1)
  obtain ⟨a, _, ha⟩ := partialOrbit_succ_some step root k x hx
  have hs := hsupport a x ha
  exact hk (by simpa [value, hx] using hs)

/-- A terminated orbit has a last defined value with no successor. -/
theorem partialOrbit_fails_has_frontier (step : Nat → Option Nat) (root : Nat) :
    ∀ n, partialOrbit step root n = none →
      ∃ k x, partialOrbit step root k = some x ∧ step x = none := by
  intro n
  induction n with
  | zero => simp [partialOrbit]
  | succ n ih =>
    intro hn
    cases hp : partialOrbit step root n with
    | none => exact ih hp
    | some x =>
      refine ⟨n, x, hp, ?_⟩
      simpa [partialOrbit, hp] using hn

/-- A finite injective path has a reachable endpoint. -/
theorem partialOrbit_has_frontier (step : Nat → Option Nat) (root : Nat)
    (support : List Nat)
    (hinj : ∀ a b x, step a = some x → step b = some x → a = b)
    (hsupport : ∀ a x, step a = some x → x ∈ support)
    (hroot : root ∉ support) :
    ∃ k x, partialOrbit step root k = some x ∧ step x = none := by
  obtain ⟨n, hn⟩ := partialOrbit_terminates step root support hinj hsupport hroot
  exact partialOrbit_fails_has_frontier step root n hn

/-- Termination occurs after at most one more step than the support length. -/
theorem partialOrbit_bounded (step : Nat → Option Nat) (root : Nat) (support : List Nat)
    (hinj : ∀ a b x, step a = some x → step b = some x → a = b)
    (hsupport : ∀ a x, step a = some x → x ∈ support)
    (hroot : root ∉ support) :
    ∃ n, n ≤ support.length + 1 ∧ partialOrbit step root n = none := by
  by_contra hnone
  have hex (n : Nat) (hn : n ≤ support.length + 1) :
      ∃ x, partialOrbit step root n = some x := by
    apply Option.ne_none_iff_exists'.1
    intro h
    exact hnone ⟨n, hn, h⟩
  have hroot' : ∀ a, step a ≠ some root := by
    intro a ha
    exact hroot (hsupport a root ha)
  let value : Nat → Nat := fun n => (partialOrbit step root (n + 1)).getD root
  have hv : Set.InjOn value (Finset.range (support.length + 1) : Set Nat) := by
    intro i hi j hj hij
    have hi' : i + 1 ≤ support.length + 1 := by simp only [Finset.mem_coe, Finset.mem_range] at hi; omega
    have hj' : j + 1 ≤ support.length + 1 := by simp only [Finset.mem_coe, Finset.mem_range] at hj; omega
    obtain ⟨x, hx⟩ := hex (i + 1) hi'
    obtain ⟨y, hy⟩ := hex (j + 1) hj'
    have hxy : x = y := by simpa [value, hx, hy] using hij
    subst y
    have he := partialOrbit_no_repeats step root hinj hroot' (i + 1) (j + 1) x hx hy
    omega
  have hsub : (Finset.range (support.length + 1)).image value ⊆ support.toFinset := by
    intro v hv'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv'
    have hi' : i + 1 ≤ support.length + 1 := by simp only [Finset.mem_range] at hi; omega
    obtain ⟨x, hx⟩ := hex (i + 1) hi'
    obtain ⟨a, _, ha⟩ := partialOrbit_succ_some step root i x hx
    apply List.mem_toFinset.mpr
    simpa [value, hx] using hsupport a x ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hv, Finset.card_range] at hc
  have hs := List.toFinset_card_le support
  omega

theorem partialOrbit_computable (step : Nat → Option Nat) (hs : Computable step) :
    Computable₂ (fun root n => partialOrbit step root n) := by
  let P := Nat × Nat
  let X := P × (Nat × Option Nat)
  have hbase : Computable (fun p : P => some p.1) :=
    (Primrec.option_some.comp Primrec.fst).to_comp
  have ho : Computable (fun p : X => p.2.2) := Computable.snd.comp Computable.snd
  have hb : Computable (fun p : X => p.2.2.bind step) :=
    Computable.option_bind ho (hs.comp Computable.snd).to₂
  have h := Computable.nat_rec (α := P) (σ := Option Nat) Computable.snd hbase hb.to₂
  have h' : Computable (fun p : P => partialOrbit step p.1 p.2) :=
    h.of_eq (fun p => by
      induction p.2 with
      | zero => rfl
      | succ n ih => simpa [partialOrbit] using congrArg (fun o => o.bind step) ih)
  exact h'.to₂

/-- Follow a path for a bounded number of steps, retaining its last value
when the successor is absent. -/
def orbitLast (step : Nat → Option Nat) (root : Nat) : Nat → Nat
  | 0 => root
  | n + 1 => (step (orbitLast step root n)).getD (orbitLast step root n)

theorem orbitLast_invariant (step : Nat → Option Nat) (root : Nat) :
    ∀ n, partialOrbit step root n = some (orbitLast step root n) ∨
      (partialOrbit step root n = none ∧ step (orbitLast step root n) = none) := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with h | ⟨hn, hs⟩
    · cases hstep : step (orbitLast step root n) with
      | none => exact Or.inr (by simp [partialOrbit, orbitLast, h, hstep])
      | some x => exact Or.inl (by simp [partialOrbit, orbitLast, h, hstep])
    · exact Or.inr (by simp [partialOrbit, orbitLast, hn, hs])

theorem partialOrbit_none_add (step : Nat → Option Nat) (root n : Nat)
    (h : partialOrbit step root n = none) :
    ∀ k, partialOrbit step root (n + k) = none := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih => simp [partialOrbit, ih]

/-- The finite-support bound gives a concrete endpoint rather than merely an
existential termination proof. -/
theorem orbitLast_endpoint (step : Nat → Option Nat) (root : Nat) (support : List Nat)
    (hinj : ∀ a b x, step a = some x → step b = some x → a = b)
    (hsupport : ∀ a x, step a = some x → x ∈ support)
    (hroot : root ∉ support) :
    step (orbitLast step root (support.length + 1)) = none := by
  obtain ⟨n, hn, hz⟩ := partialOrbit_bounded step root support hinj hsupport hroot
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have he : partialOrbit step root (support.length + 1) = none := by
    rw [hk]
    exact partialOrbit_none_add step root n hz k
  rcases orbitLast_invariant step root (support.length + 1) with h | h
  · simp [he] at h
  · exact h.2

theorem orbitLast_computable (step : Nat → Option Nat) (hs : Computable step) :
    Computable₂ (fun root n => orbitLast step root n) := by
  let P := Nat × Nat
  let X := P × (Nat × Nat)
  have hbase : Computable (fun p : P => p.1) := Computable.fst
  have hprev : Computable (fun p : X => p.2.2) := Computable.snd.comp Computable.snd
  have hstep : Computable (fun p : X => (step p.2.2).getD p.2.2) :=
    (hs.comp hprev).option_getD hprev
  have h := Computable.nat_rec (α := P) (σ := Nat) Computable.snd hbase hstep.to₂
  have h' : Computable (fun p : P => orbitLast step p.1 p.2) :=
    h.of_eq (fun p => by
      induction p.2 with
      | zero => rfl
      | succ n ih => simpa [orbitLast] using congrArg (fun x => (step x).getD x) ih)
  exact h'.to₂

/-- The retained value is always one of the values actually visited. -/
theorem orbitLast_reachable (step : Nat → Option Nat) (root : Nat) :
    ∀ n, ∃ k, k ≤ n ∧ partialOrbit step root k = some (orbitLast step root n) := by
  intro n
  induction n with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ n ih =>
    cases hstep : step (orbitLast step root n) with
    | none =>
      obtain ⟨k, hk, hv⟩ := ih
      refine ⟨k, by omega, ?_⟩
      simpa [orbitLast, hstep] using hv
    | some x =>
      rcases orbitLast_invariant step root n with h | ⟨_, hn⟩
      · refine ⟨n + 1, by omega, ?_⟩
        simp [partialOrbit, orbitLast, h, hstep]
      · simp [hstep] at hn

/-- One orientation of the augmentation path: follow a reduction and then
follow an existing matching edge backwards. -/
def matchingStep (f : Nat → Nat) (back : Nat → Option Nat) (x : Nat) : Option Nat :=
  back (f x)

theorem matchingStep_injective (f : Nat → Nat) (back : Nat → Option Nat)
    (hf : Function.Injective f)
    (hb : ∀ a b x, back a = some x → back b = some x → a = b) :
    ∀ a b x, matchingStep f back a = some x → matchingStep f back b = some x → a = b := by
  intro a b x ha hb'
  exact hf (hb (f a) (f b) x ha hb')

theorem matchingStep_computable (f : Nat → Nat) (back : Nat → Option Nat)
    (hf : Computable f) (hb : Computable back) : Computable (matchingStep f back) :=
  hb.comp hf

theorem matchingStep_preserves (A B : Nat → Prop) (f : Nat → Nat)
    (back : Nat → Option Nat)
    (hf : ∀ x, A x ↔ B (f x))
    (hb : ∀ y x, back y = some x → (B y ↔ A x))
    {a x : Nat} (h : matchingStep f back a = some x) : A a ↔ A x :=
  (hf a).trans (hb (f a) x h)

theorem partialOrbit_preserves (A : Nat → Prop) (step : Nat → Option Nat)
    (hstep : ∀ a x, step a = some x → (A a ↔ A x)) (root : Nat) :
    ∀ n x, partialOrbit step root n = some x → (A root ↔ A x) := by
  intro n
  induction n with
  | zero =>
    intro x h
    have hx : root = x := by simpa [partialOrbit] using h
    subst x
    rfl
  | succ n ih =>
    intro x h
    obtain ⟨a, ha, hx⟩ := partialOrbit_succ_some step root n x h
    exact (ih a ha).trans (hstep a x hx)

/-- A forward augmentation path effectively reaches an unmatched target while
preserving the source-language status of its root. The reverse orientation is
the same statement with the two languages and reductions exchanged. -/
theorem matching_endpoint (A B : Nat → Prop) (f : Nat → Nat)
    (back : Nat → Option Nat) (root : Nat) (support : List Nat)
    (hf : Function.Injective f)
    (hb : ∀ a b x, back a = some x → back b = some x → a = b)
    (hsupport : ∀ y x, back y = some x → x ∈ support)
    (hroot : root ∉ support)
    (hfred : ∀ x, A x ↔ B (f x))
    (hbrel : ∀ y x, back y = some x → (B y ↔ A x)) :
    let endpoint := orbitLast (matchingStep f back) root (support.length + 1)
    back (f endpoint) = none ∧ (A root ↔ B (f endpoint)) := by
  dsimp only
  have hstepinj := matchingStep_injective f back hf hb
  have hstepsup : ∀ a x, matchingStep f back a = some x → x ∈ support := by
    intro a x ha
    exact hsupport (f a) x ha
  have hend := orbitLast_endpoint (matchingStep f back) root support hstepinj hstepsup hroot
  obtain ⟨k, _, hk⟩ := orbitLast_reachable (matchingStep f back) root (support.length + 1)
  have hrel := partialOrbit_preserves A (matchingStep f back)
    (fun a x ha => matchingStep_preserves A B f back hfred hbrel ha) root k _ hk
  exact ⟨hend, hrel.trans (hfred _)⟩

#print axioms partialOrbit_no_repeats
#print axioms partialOrbit_terminates
#print axioms partialOrbit_has_frontier
#print axioms partialOrbit_bounded
#print axioms partialOrbit_computable
#print axioms orbitLast_endpoint
#print axioms orbitLast_computable
#print axioms matching_endpoint
#print axioms matchingStep_computable
end LambdaTuring
