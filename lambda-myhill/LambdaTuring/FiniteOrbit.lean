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

#print axioms partialOrbit_no_repeats
#print axioms partialOrbit_terminates
#print axioms partialOrbit_has_frontier
#print axioms partialOrbit_computable
end LambdaTuring
