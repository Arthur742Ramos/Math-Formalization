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

/-- Replace the edge ending at `y` by the edge from an unmatched `x` to `y`.
If `y` was matched, its old source becomes the new unmatched source. -/
def spliceForward (forward : Nat → Option Nat) (x y u : Nat) : Option Nat :=
  if u = x then some y else if forward u = some y then none else forward u

def spliceBackward (backward : Nat → Option Nat) (x y v : Nat) : Option Nat :=
  if v = y then some x else backward v

theorem splice_inverse (forward backward : Nat → Option Nat) (x y : Nat)
    (hinv : ∀ u v, forward u = some v ↔ backward v = some u)
    (hfresh : forward x = none) :
    ∀ u v, spliceForward forward x y u = some v ↔
      spliceBackward backward x y v = some u := by
  have hback (v : Nat) : backward v ≠ some x := by
    intro h
    have h' := (hinv x v).2 h
    rw [hfresh] at h'
    contradiction
  intro u v
  by_cases hx : u = x
  · subst u
    by_cases hy : v = y
    · simp [spliceForward, spliceBackward, hy]
    · simp [spliceForward, spliceBackward, hy, Ne.symm hy, hback]
  · by_cases hy : v = y
    · subst v
      by_cases htarget : forward u = some y <;>
        simp [spliceForward, spliceBackward, hx, Ne.symm hx, htarget]
    · by_cases htarget : forward u = some y
      · have hv : backward v ≠ some u := by
          intro h
          have h' := (hinv u v).2 h
          rw [htarget] at h'
          exact hy (Option.some.inj h').symm
        simp [spliceForward, spliceBackward, hx, hy, htarget, hv]
      · simpa [spliceForward, spliceBackward, hx, hy, htarget] using hinv u v

theorem splice_preserves (forward : Nat → Option Nat) (x y : Nat) (A B : Nat → Prop)
    (hrel : ∀ u v, forward u = some v → (A u ↔ B v))
    (hnew : A x ↔ B y) :
    ∀ u v, spliceForward forward x y u = some v → (A u ↔ B v) := by
  intro u v h
  by_cases hx : u = x
  · subst u
    have hv : y = v := by simpa [spliceForward] using h
    simpa [← hv] using hnew
  · by_cases htarget : forward u = some y
    · simp [spliceForward, hx, htarget] at h
    · exact hrel u v (by simpa [spliceForward, hx, htarget] using h)

theorem splice_displaces (forward backward : Nat → Option Nat) (x y a : Nat)
    (hinv : ∀ u v, forward u = some v ↔ backward v = some u)
    (hfresh : forward x = none) (hold : backward y = some a) :
    spliceForward forward x y a = none := by
  have ha : forward a = some y := (hinv a y).2 hold
  have hax : a ≠ x := by
    intro h
    subst a
    rw [hfresh] at ha
    contradiction
  simp [spliceForward, hax, ha]

theorem splice_new_edge (forward backward : Nat → Option Nat) (x y : Nat) :
    spliceForward forward x y x = some y ∧ spliceBackward backward x y y = some x := by
  simp [spliceForward, spliceBackward]

theorem splice_backward_other (backward : Nat → Option Nat) (x y v : Nat) (h : v ≠ y) :
    spliceBackward backward x y v = backward v := by
  simp [spliceBackward, h]

theorem splice_forward_other (forward : Nat → Option Nat) (x y u : Nat)
    (hx : u ≠ x) (hy : forward u ≠ some y) :
    spliceForward forward x y u = forward u := by
  simp [spliceForward, hx, hy]

theorem splice_forward_support (forward : Nat → Option Nat) (x y : Nat) (support : List Nat)
    (hsupport : ∀ u v, forward u = some v → u ∈ support) :
    ∀ u v, spliceForward forward x y u = some v → u ∈ x :: support := by
  intro u v h
  by_cases hx : u = x
  · simp [hx]
  · have hold : forward u = some v := by
      by_cases hy : forward u = some y
      · simp [spliceForward, hx, hy] at h
      · simpa [spliceForward, hx, hy] using h
    simp [hx, hsupport u v hold]

theorem spliceForward_computable (forward : Nat → Option Nat) (x y : Nat)
    (hf : Computable forward) : Computable (spliceForward forward x y) := by
  have hx : Computable (fun u : Nat => decide (u = x)) :=
    (Primrec.eq.decide.comp Primrec.id (Primrec.const x)).to_comp
  have hy : Computable (fun u : Nat => decide (forward u = some y)) :=
    (Primrec.eq : PrimrecRel (fun a b : Option Nat => a = b)).decide.to_comp.comp
      hf (Computable.const (some y))
  have h := Computable.cond hx (Computable.const (some y))
    (Computable.cond hy (Computable.const none) hf)
  exact h.of_eq (fun u => by simp [spliceForward])

theorem spliceBackward_computable (backward : Nat → Option Nat) (x y : Nat)
    (hb : Computable backward) : Computable (spliceBackward backward x y) := by
  have hy : Computable (fun v : Nat => decide (v = y)) :=
    (Primrec.eq.decide.comp Primrec.id (Primrec.const y)).to_comp
  have h := Computable.cond hy (Computable.const (some x)) hb
  exact h.of_eq (fun v => by simp [spliceBackward])

/-- If the target was unmatched, splicing extends every old edge. -/
theorem splice_extends_of_free (forward backward : Nat → Option Nat) (x y : Nat)
    (hinv : ∀ u v, forward u = some v ↔ backward v = some u)
    (hfresh : forward x = none) (hfree : backward y = none) :
    ∀ u v, forward u = some v → spliceForward forward x y u = some v := by
  intro u v h
  have hx : u ≠ x := by
    intro heq
    subst u
    rw [hfresh] at h
    contradiction
  have hy : forward u ≠ some y := by
    intro heq
    have h' := (hinv u y).1 heq
    rw [hfree] at h'
    contradiction
  simpa [splice_forward_other forward x y u hx hy] using h

/-- A single forward augmentation preserves the partial matching and the
language invariant; it either extends the old matching at a free target or
displaces a source with the same language status as the new source. -/
theorem splice_progress (forward backward : Nat → Option Nat) (x y : Nat)
    (A B : Nat → Prop) (support : List Nat)
    (hinv : ∀ u v, forward u = some v ↔ backward v = some u)
    (hfresh : forward x = none)
    (hrel : ∀ u v, forward u = some v → (A u ↔ B v))
    (hnew : A x ↔ B y)
    (hsupport : ∀ u v, forward u = some v → u ∈ support) :
    (∀ u v, spliceForward forward x y u = some v ↔
      spliceBackward backward x y v = some u) ∧
    (∀ u v, spliceForward forward x y u = some v → (A u ↔ B v)) ∧
    (∀ u v, spliceForward forward x y u = some v → u ∈ x :: support) ∧
    (backward y = none → ∀ u v, forward u = some v → spliceForward forward x y u = some v) ∧
    (∀ a, backward y = some a → spliceForward forward x y a = none ∧ (A a ↔ A x)) := by
  refine ⟨splice_inverse forward backward x y hinv hfresh,
    splice_preserves forward x y A B hrel hnew,
    splice_forward_support forward x y support hsupport, ?_, ?_⟩
  · exact splice_extends_of_free forward backward x y hinv hfresh
  · intro a ha
    refine ⟨splice_displaces forward backward x y a hinv hfresh ha, ?_⟩
    exact (hrel a y ((hinv a y).2 ha)).trans hnew.symm

/-- A computable increasing sequence of compatible partial matchings that
covers both sides determines computable inverse maps. -/
theorem computable_equiv_of_matchings (A B : Nat → Prop)
    (forward backward : Nat → Nat → Option Nat)
    (hf : Computable₂ forward) (hb : Computable₂ backward)
    (hinv : ∀ n x y, forward n x = some y ↔ backward n y = some x)
    (hmono : ∀ m n x y, m ≤ n → forward m x = some y → forward n x = some y)
    (hcoverF : ∀ x, ∃ n y, forward n x = some y)
    (hcoverB : ∀ y, ∃ n x, backward n y = some x)
    (hrel : ∀ n x y, forward n x = some y → (A x ↔ B y)) :
    ∃ f g : Nat → Nat, Computable f ∧ Computable g ∧
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧ (∀ x, A x ↔ B (f x)) := by
  let pf : Nat → Part Nat := fun x => Nat.rfindOpt (fun n => forward n x)
  let pb : Nat → Part Nat := fun y => Nat.rfindOpt (fun n => backward n y)
  have hpf : Partrec pf := Partrec.rfindOpt (hf.comp Computable.snd Computable.fst).to₂
  have hpb : Partrec pb := Partrec.rfindOpt (hb.comp Computable.snd Computable.fst).to₂
  have hdomf (x : Nat) : (pf x).Dom := by
    apply Nat.rfindOpt_dom.mpr
    obtain ⟨n, y, h⟩ := hcoverF x
    exact ⟨n, y, Option.mem_def.mpr h⟩
  have hdomb (y : Nat) : (pb y).Dom := by
    apply Nat.rfindOpt_dom.mpr
    obtain ⟨n, x, h⟩ := hcoverB y
    exact ⟨n, x, Option.mem_def.mpr h⟩
  let f : Nat → Nat := fun x => (pf x).get (hdomf x)
  let g : Nat → Nat := fun y => (pb y).get (hdomb y)
  have hfc : Computable f := hpf.of_eq_tot (fun x => Part.get_mem (hdomf x))
  have hgc : Computable g := hpb.of_eq_tot (fun y => Part.get_mem (hdomb y))
  have hbm (m n y x : Nat) (hmn : m ≤ n) (h : backward m y = some x) :
      backward n y = some x :=
    (hinv n x y).1 (hmono m n x y hmn ((hinv m x y).2 h))
  have hgf (x : Nat) : g (f x) = x := by
    have hmem : f x ∈ pf x := Part.get_mem (hdomf x)
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
    have hback : backward n (f x) = some x := (hinv n x (f x)).1 (Option.mem_def.mp hn)
    have hx : x ∈ pb (f x) := (Nat.rfindOpt_mono (fun {a m n} hmn h => by
      exact Option.mem_def.mpr (hbm m n (f x) a hmn (Option.mem_def.mp h)))).2
      ⟨n, Option.mem_def.mpr hback⟩
    exact Part.mem_unique (Part.get_mem (hdomb (f x))) hx
  have hfg (y : Nat) : f (g y) = y := by
    have hmem : g y ∈ pb y := Part.get_mem (hdomb y)
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
    have hfor : forward n (g y) = some y := (hinv n (g y) y).2 (Option.mem_def.mp hn)
    have hy : y ∈ pf (g y) := (Nat.rfindOpt_mono (fun {a m n} hmn h => by
      exact Option.mem_def.mpr (hmono m n (g y) a hmn (Option.mem_def.mp h)))).2
      ⟨n, Option.mem_def.mpr hfor⟩
    exact Part.mem_unique (Part.get_mem (hdomf (g y))) hy
  refine ⟨f, g, hfc, hgc, hgf, hfg, ?_⟩
  intro x
  have hmem : f x ∈ pf x := Part.get_mem (hdomf x)
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
  exact hrel n x (f x) (Option.mem_def.mp hn)

#print axioms partialOrbit_no_repeats
#print axioms partialOrbit_terminates
#print axioms partialOrbit_has_frontier
#print axioms partialOrbit_bounded
#print axioms partialOrbit_computable
#print axioms orbitLast_endpoint
#print axioms orbitLast_computable
#print axioms matching_endpoint
#print axioms matchingStep_computable
#print axioms splice_inverse
#print axioms splice_preserves
#print axioms splice_displaces
#print axioms splice_forward_support
#print axioms spliceForward_computable
#print axioms spliceBackward_computable
#print axioms splice_progress
#print axioms computable_equiv_of_matchings
end LambdaTuring
