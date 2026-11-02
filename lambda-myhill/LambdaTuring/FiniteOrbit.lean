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

/-- Lookup in a finite list of natural-number edges. -/
def edgeLookup : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (a, b) :: xs, x => if x = a then some b else edgeLookup xs x

theorem edgeLookup_sound (xs : List (Nat × Nat)) (x y : Nat)
    (h : edgeLookup xs x = some y) : (x, y) ∈ xs := by
  induction xs with
  | nil => simp [edgeLookup] at h
  | cons ab xs ih =>
    obtain ⟨a, b⟩ := ab
    by_cases hx : x = a
    · subst x
      have hy : b = y := by simpa [edgeLookup] using h
      subst y
      simp
    · have ht : edgeLookup xs x = some y := by simpa [edgeLookup, hx] using h
      exact List.mem_cons_of_mem _ (ih ht)

theorem edgeLookup_complete (xs : List (Nat × Nat))
    (hunique : ∀ x y z, (x, y) ∈ xs → (x, z) ∈ xs → y = z)
    (x y : Nat) (h : (x, y) ∈ xs) : edgeLookup xs x = some y := by
  induction xs with
  | nil => simp at h
  | cons ab xs ih =>
    obtain ⟨a, b⟩ := ab
    by_cases hx : x = a
    · subst x
      have hy : b = y := hunique a b y (by simp) h
      simp [edgeLookup, hy]
    · have ht : (x, y) ∈ xs := by simpa [hx] using h
      have hu : ∀ x y z, (x, y) ∈ xs → (x, z) ∈ xs → y = z := by
        intro x y z h1 h2
        exact hunique x y z (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)
      simpa [edgeLookup, hx] using ih hu ht

theorem edgeLookup_primrec : Primrec₂ edgeLookup := by
  let P := List (Nat × Nat) × Nat
  let X := P × ((Nat × Nat) × (List (Nat × Nat) × Option Nat))
  have hl : Primrec (fun p : P => p.1) := Primrec.fst
  have hz : Primrec (fun _ : P => (none : Option Nat)) := Primrec.const _
  have heq : PrimrecPred (fun q : X => q.1.2 = q.2.1.1) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hval : Primrec (fun q : X => some q.2.1.2) :=
    Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hrest : Primrec (fun q : X => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec (fun q : X => if q.1.2 = q.2.1.1 then some q.2.1.2 else q.2.2.2) :=
    Primrec.ite heq hval hrest
  have hr := Primrec.list_rec hl hz hstep.to₂
  have hr' : Primrec (fun p : P => edgeLookup p.1 p.2) :=
    hr.of_eq (fun p => by induction p.1 with
      | nil => rfl
      | cons a xs ih => cases a; simp [edgeLookup, ih])
  exact hr'.to₂

def reverseEdges (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  xs.map (fun p => (p.2, p.1))

theorem reverseEdges_mem (xs : List (Nat × Nat)) (x y : Nat) :
    (y, x) ∈ reverseEdges xs ↔ (x, y) ∈ xs := by
  induction xs with
  | nil => simp [reverseEdges]
  | cons p xs ih =>
    obtain ⟨a, b⟩ := p
    simp [reverseEdges, Prod.mk.injEq, and_comm]

def edgeSourceUnique (xs : List (Nat × Nat)) : Prop :=
  ∀ x y z, (x, y) ∈ xs → (x, z) ∈ xs → y = z

def edgeMatching (A B : Nat → Prop) (xs : List (Nat × Nat)) : Prop :=
  edgeSourceUnique xs ∧ edgeSourceUnique (reverseEdges xs) ∧
    ∀ x y, (x, y) ∈ xs → (A x ↔ B y)

def edgeForward (xs : List (Nat × Nat)) (x : Nat) : Option Nat := edgeLookup xs x

def edgeBackward (xs : List (Nat × Nat)) (y : Nat) : Option Nat :=
  edgeLookup (reverseEdges xs) y

theorem edgeMatching_inverse (A B : Nat → Prop) (xs : List (Nat × Nat))
    (hm : edgeMatching A B xs) :
    ∀ x y, edgeForward xs x = some y ↔ edgeBackward xs y = some x := by
  intro x y
  constructor
  · intro h
    apply edgeLookup_complete (reverseEdges xs) hm.2.1
    exact (reverseEdges_mem xs x y).2 (edgeLookup_sound xs x y h)
  · intro h
    apply edgeLookup_complete xs hm.1
    exact (reverseEdges_mem xs x y).1 (edgeLookup_sound (reverseEdges xs) y x h)

theorem edgeMatching_back_injective (A B : Nat → Prop) (xs : List (Nat × Nat))
    (hm : edgeMatching A B xs) :
    ∀ a b x, edgeBackward xs a = some x → edgeBackward xs b = some x → a = b := by
  intro a b x ha hb
  apply hm.1 x a b
  · exact (reverseEdges_mem xs x a).1 (edgeLookup_sound (reverseEdges xs) a x ha)
  · exact (reverseEdges_mem xs x b).1 (edgeLookup_sound (reverseEdges xs) b x hb)

theorem edgeMatching_back_rel (A B : Nat → Prop) (xs : List (Nat × Nat))
    (hm : edgeMatching A B xs) :
    ∀ y x, edgeBackward xs y = some x → (B y ↔ A x) := by
  intro y x h
  exact (hm.2.2 x y ((reverseEdges_mem xs x y).1
    (edgeLookup_sound (reverseEdges xs) y x h))).symm

theorem edgeMatching_back_support (xs : List (Nat × Nat)) :
    ∀ y x, edgeBackward xs y = some x → x ∈ xs.map Prod.fst := by
  intro y x h
  have hm := (reverseEdges_mem xs x y).1 (edgeLookup_sound (reverseEdges xs) y x h)
  exact List.mem_map.mpr ⟨(x, y), hm, rfl⟩

theorem edgeMatching_fresh (A B : Nat → Prop) (xs : List (Nat × Nat))
    (hm : edgeMatching A B xs) (x : Nat) (h : edgeForward xs x = none) :
    x ∉ xs.map Prod.fst := by
  intro hx
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hx
  obtain ⟨a, b⟩ := p
  dsimp only at heq
  subst a
  have h' := edgeLookup_complete xs hm.1 x b hp
  change edgeLookup xs x = none at h
  rw [h] at h'
  contradiction

theorem edgeSourceUnique_cons (xs : List (Nat × Nat)) (x y : Nat)
    (hu : edgeSourceUnique xs) (hfresh : edgeLookup xs x = none) :
    edgeSourceUnique ((x, y) :: xs) := by
  have hnot (v : Nat) : (x, v) ∉ xs := by
    intro h
    have h' := edgeLookup_complete xs hu x v h
    rw [hfresh] at h'
    contradiction
  intro a b c h1 h2
  simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨ha, hb⟩ | h1
  · subst a
    subst b
    rcases h2 with ⟨_, hc⟩ | h2
    · exact hc.symm
    · exact False.elim (hnot c h2)
  · rcases h2 with ⟨ha, hc⟩ | h2
    · subst a
      exact False.elim (hnot b h1)
    · exact hu a b c h1 h2

theorem edgeMatching_cons (A B : Nat → Prop) (xs : List (Nat × Nat))
    (x y : Nat) (hm : edgeMatching A B xs)
    (hx : edgeForward xs x = none) (hy : edgeBackward xs y = none)
    (hrel : A x ↔ B y) : edgeMatching A B ((x, y) :: xs) := by
  refine ⟨edgeSourceUnique_cons xs x y hm.1 hx, ?_, ?_⟩
  · simpa [reverseEdges] using edgeSourceUnique_cons (reverseEdges xs) y x hm.2.1 hy
  · intro a b h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨ha, hb⟩ | h
    · subst a
      subst b
      exact hrel
    · exact hm.2.2 a b h

/-- Add a free edge at a target reached by an alternating path. -/
def extendLeft (f : Nat → Nat) (xs : List (Nat × Nat)) (x : Nat) : List (Nat × Nat) :=
  match edgeForward xs x with
  | some _ => xs
  | none =>
    let endpoint := orbitLast (matchingStep f (edgeBackward xs)) x (xs.length + 1)
    (x, f endpoint) :: xs

theorem extendLeft_spec (A B : Nat → Prop) (f : Nat → Nat)
    (hf : Function.Injective f) (hred : ∀ x, A x ↔ B (f x))
    (xs : List (Nat × Nat)) (hm : edgeMatching A B xs) (x : Nat) :
    edgeMatching A B (extendLeft f xs x) ∧
      (∀ a b, (a, b) ∈ xs → (a, b) ∈ extendLeft f xs x) ∧
      (∃ y, (x, y) ∈ extendLeft f xs x) := by
  cases hx : edgeForward xs x with
  | some y =>
    have hxy : (x, y) ∈ xs := edgeLookup_sound xs x y hx
    exact ⟨by simpa [extendLeft, hx] using hm,
      by intro a b h; simpa [extendLeft, hx] using h,
      ⟨y, by simpa [extendLeft, hx] using hxy⟩⟩
  | none =>
    have hroot := edgeMatching_fresh A B xs hm x hx
    have he := matching_endpoint A B f (edgeBackward xs) x (xs.map Prod.fst)
      hf (edgeMatching_back_injective A B xs hm) (edgeMatching_back_support xs)
      hroot hred (edgeMatching_back_rel A B xs hm)
    have he' :
      edgeBackward xs (f (orbitLast (matchingStep f (edgeBackward xs)) x (xs.length + 1))) = none ∧
      (A x ↔ B (f (orbitLast (matchingStep f (edgeBackward xs)) x (xs.length + 1)))) := by
      simpa using he
    refine ⟨?_, ?_, ?_⟩
    · simpa [extendLeft, hx] using edgeMatching_cons A B xs x _ hm hx he'.1 he'.2
    · intro a b h
      simpa [extendLeft, hx] using List.mem_cons_of_mem (x, f (orbitLast (matchingStep f (edgeBackward xs)) x (xs.length + 1))) h
    · exact ⟨f (orbitLast (matchingStep f (edgeBackward xs)) x (xs.length + 1)),
        by simp [extendLeft, hx]⟩

theorem reverseEdges_involutive (xs : List (Nat × Nat)) : reverseEdges (reverseEdges xs) = xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨a, b⟩ := p
    simp [reverseEdges, List.map_map, Function.comp_def]

theorem edgeMatching_reverse (A B : Nat → Prop) (xs : List (Nat × Nat))
    (hm : edgeMatching A B xs) : edgeMatching B A (reverseEdges xs) := by
  refine ⟨hm.2.1, ?_, ?_⟩
  · simpa [reverseEdges_involutive] using hm.1
  · intro y x h
    exact (hm.2.2 x y ((reverseEdges_mem xs x y).1 h)).symm

def extendRight (g : Nat → Nat) (xs : List (Nat × Nat)) (y : Nat) : List (Nat × Nat) :=
  reverseEdges (extendLeft g (reverseEdges xs) y)

theorem extendRight_spec (A B : Nat → Prop) (g : Nat → Nat)
    (hg : Function.Injective g) (hred : ∀ y, B y ↔ A (g y))
    (xs : List (Nat × Nat)) (hm : edgeMatching A B xs) (y : Nat) :
    edgeMatching A B (extendRight g xs y) ∧
      (∀ a b, (a, b) ∈ xs → (a, b) ∈ extendRight g xs y) ∧
      (∃ x, (x, y) ∈ extendRight g xs y) := by
  obtain ⟨hvalid, hext, hcov⟩ := extendLeft_spec B A g hg hred
    (reverseEdges xs) (edgeMatching_reverse A B xs hm) y
  refine ⟨edgeMatching_reverse B A _ hvalid, ?_, ?_⟩
  · intro a b h
    apply (reverseEdges_mem _ b a).2
    exact hext b a ((reverseEdges_mem xs a b).2 h)
  · obtain ⟨x, hx⟩ := hcov
    exact ⟨x, (reverseEdges_mem _ y x).2 hx⟩

theorem reverseEdges_primrec : Primrec reverseEdges := by
  have hswap : Primrec (fun p : Nat × Nat => (p.2, p.1)) := Primrec.snd.pair Primrec.fst
  have h := Primrec.list_map (Primrec.id : Primrec (fun xs : List (Nat × Nat) => xs))
    (hswap.comp Primrec.snd).to₂
  exact h.of_eq (fun _ => rfl)

theorem edgeBackward_primrec : Primrec₂ edgeBackward := by
  have h := edgeLookup_primrec.comp (reverseEdges_primrec.comp Primrec.fst) Primrec.snd
  exact h.to₂

/-- Uniformly compute the bounded path when both the finite matching and the
root vary. -/
theorem matchingLast_computable (f : Nat → Nat) (hf : Computable f) :
    Computable (fun p : (List (Nat × Nat) × Nat) × Nat =>
      orbitLast (matchingStep f (edgeBackward p.1.1)) p.1.2 p.2) := by
  let P := (List (Nat × Nat) × Nat) × Nat
  let X := P × (Nat × Nat)
  have hbase : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have hxs : Computable (fun q : X => q.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hprev : Computable (fun q : X => q.2.2) := Computable.snd.comp Computable.snd
  have hnext : Computable (fun q : X => edgeBackward q.1.1.1 (f q.2.2)) :=
    edgeBackward_primrec.to_comp.comp hxs (hf.comp hprev)
  have hstep : Computable (fun q : X => (edgeBackward q.1.1.1 (f q.2.2)).getD q.2.2) :=
    hnext.option_getD hprev
  have h := Computable.nat_rec (α := P) (σ := Nat) Computable.snd hbase hstep.to₂
  have heq (p : P) :
      Nat.rec p.1.2 (fun _ x => (edgeBackward p.1.1 (f x)).getD x) p.2 =
        orbitLast (matchingStep f (edgeBackward p.1.1)) p.1.2 p.2 := by
    obtain ⟨⟨xs, x⟩, n⟩ := p
    induction n with
    | zero => rfl
    | succ n ih => simp [orbitLast, matchingStep, ih]
  exact h.of_eq heq

theorem extendLeft_computable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (extendLeft f) := by
  let P := List (Nat × Nat) × Nat
  have hlookup : Computable (fun p : P => edgeForward p.1 p.2) :=
    edgeLookup_primrec.to_comp
  have hsome : Computable (fun p : P => (edgeForward p.1 p.2).isSome) :=
    Primrec.option_isSome.to_comp.comp hlookup
  have hbound : Computable (fun p : P => p.1.length + 1) :=
    Computable.succ.comp (Computable.list_length.comp Computable.fst)
  have hlast : Computable (fun p : P =>
      orbitLast (matchingStep f (edgeBackward p.1)) p.2 (p.1.length + 1)) :=
    (matchingLast_computable f hf).comp (Computable.id.pair hbound)
  have hnew : Computable (fun p : P =>
      (p.2, f (orbitLast (matchingStep f (edgeBackward p.1)) p.2 (p.1.length + 1))) :: p.1) :=
    Computable.list_cons.comp (Computable.snd.pair (hf.comp hlast)) Computable.fst
  have h := Computable.cond hsome Computable.fst hnew
  have h' : Computable (fun p : P => extendLeft f p.1 p.2) :=
    h.of_eq (fun p => by cases he : edgeForward p.1 p.2 <;> simp [extendLeft, he])
  exact h'.to₂

theorem extendRight_computable (g : Nat → Nat) (hg : Computable g) :
    Computable₂ (extendRight g) := by
  have h : Computable (fun p : List (Nat × Nat) × Nat =>
      reverseEdges (extendLeft g (reverseEdges p.1) p.2)) :=
    reverseEdges_primrec.to_comp.comp
      ((extendLeft_computable g hg).comp (reverseEdges_primrec.to_comp.comp Computable.fst) Computable.snd)
  exact h.to₂

/-- At stage `n`, cover `n` on the source side and then on the target side. -/
def matchingStages (f g : Nat → Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => extendRight g (extendLeft f (matchingStages f g n) n) n

theorem matchingStages_computable (f g : Nat → Nat) (hf : Computable f) (hg : Computable g) :
    Computable (matchingStages f g) := by
  let X := Nat × (Nat × List (Nat × Nat))
  have hn : Computable (fun q : X => q.2.1) := Computable.fst.comp Computable.snd
  have hxs : Computable (fun q : X => q.2.2) := Computable.snd.comp Computable.snd
  have hl := (extendLeft_computable f hf).comp hxs hn
  have hstep : Computable (fun q : X => extendRight g (extendLeft f q.2.2 q.2.1) q.2.1) :=
    (extendRight_computable g hg).comp hl hn
  have h := Computable.nat_rec (α := Nat) (σ := List (Nat × Nat)) Computable.id
    (Computable.const []) hstep.to₂
  have heq (n : Nat) :
      Nat.rec [] (fun k xs => extendRight g (extendLeft f xs k) k) n = matchingStages f g n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [matchingStages, ih]
  exact h.of_eq heq

theorem matchingStages_valid (A B : Nat → Prop) (f g : Nat → Nat)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, A x ↔ B (f x)) (hgr : ∀ y, B y ↔ A (g y)) :
    ∀ n, edgeMatching A B (matchingStages f g n) := by
  intro n
  induction n with
  | zero => simp [matchingStages, edgeMatching, edgeSourceUnique, reverseEdges]
  | succ n ih =>
    have hl := (extendLeft_spec A B f hfi hfr (matchingStages f g n) ih n).1
    have hr := (extendRight_spec A B g hgi hgr (extendLeft f (matchingStages f g n) n) hl n).1
    simpa [matchingStages] using hr

theorem matchingStages_step (A B : Nat → Prop) (f g : Nat → Nat)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, A x ↔ B (f x)) (hgr : ∀ y, B y ↔ A (g y)) (n : Nat) :
    (∀ x y, (x, y) ∈ matchingStages f g n → (x, y) ∈ matchingStages f g (n + 1)) ∧
    (∃ y, (n, y) ∈ matchingStages f g (n + 1)) ∧
    (∃ x, (x, n) ∈ matchingStages f g (n + 1)) := by
  have hv := matchingStages_valid A B f g hfi hgi hfr hgr n
  obtain ⟨hlv, hle, hlc⟩ := extendLeft_spec A B f hfi hfr (matchingStages f g n) hv n
  obtain ⟨_, hre, hrc⟩ := extendRight_spec A B g hgi hgr (extendLeft f (matchingStages f g n) n) hlv n
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    exact hre x y (hle x y h)
  · obtain ⟨y, hy⟩ := hlc
    exact ⟨y, hre n y hy⟩
  · exact hrc

theorem matchingStages_mono (A B : Nat → Prop) (f g : Nat → Nat)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, A x ↔ B (f x)) (hgr : ∀ y, B y ↔ A (g y))
    (m n x y : Nat) (h : m ≤ n) :
    (x, y) ∈ matchingStages f g m → (x, y) ∈ matchingStages f g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
    intro he
    exact (matchingStages_step A B f g hfi hgi hfr hgr (m + k)).1 x y (ih (by omega) he)

/-- Effective isomorphism theorem: mutually injective computable reductions
give computable inverse bijections preserving language membership. -/
theorem effective_isomorphism_of_oneOne (A B : Nat → Prop) (f g : Nat → Nat)
    (hfc : Computable f) (hgc : Computable g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, A x ↔ B (f x)) (hgr : ∀ y, B y ↔ A (g y)) :
    ∃ u v : Nat → Nat, Computable u ∧ Computable v ∧
      (∀ x, v (u x) = x) ∧ (∀ y, u (v y) = y) ∧ (∀ x, A x ↔ B (u x)) := by
  let stages := matchingStages f g
  let forward : Nat → Nat → Option Nat := fun n x => edgeForward (stages n) x
  let backward : Nat → Nat → Option Nat := fun n y => edgeBackward (stages n) y
  have hs : Computable stages := matchingStages_computable f g hfc hgc
  have hforward : Computable₂ forward := by
    have h : Computable (fun p : Nat × Nat => edgeForward (stages p.1) p.2) :=
      edgeLookup_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd
    exact h.to₂
  have hbackward : Computable₂ backward := by
    have h : Computable (fun p : Nat × Nat => edgeBackward (stages p.1) p.2) :=
      edgeBackward_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd
    exact h.to₂
  have hv (n : Nat) : edgeMatching A B (stages n) :=
    matchingStages_valid A B f g hfi hgi hfr hgr n
  have hi : ∀ n x y, forward n x = some y ↔ backward n y = some x := by
    intro n
    exact edgeMatching_inverse A B (stages n) (hv n)
  have hm : ∀ m n x y, m ≤ n → forward m x = some y → forward n x = some y := by
    intro m n x y hmn h
    apply edgeLookup_complete (stages n) (hv n).1
    exact matchingStages_mono A B f g hfi hgi hfr hgr m n x y hmn
      (edgeLookup_sound (stages m) x y h)
  have hcF : ∀ x, ∃ n y, forward n x = some y := by
    intro x
    obtain ⟨y, hy⟩ := (matchingStages_step A B f g hfi hgi hfr hgr x).2.1
    exact ⟨x + 1, y, edgeLookup_complete (stages (x + 1)) (hv (x + 1)).1 x y hy⟩
  have hcB : ∀ y, ∃ n x, backward n y = some x := by
    intro y
    obtain ⟨x, hx⟩ := (matchingStages_step A B f g hfi hgi hfr hgr y).2.2
    have hfor := edgeLookup_complete (stages (y + 1)) (hv (y + 1)).1 x y hx
    exact ⟨y + 1, x, (hi (y + 1) x y).1 hfor⟩
  have hr : ∀ n x y, forward n x = some y → (A x ↔ B y) := by
    intro n x y h
    exact (hv n).2.2 x y (edgeLookup_sound (stages n) x y h)
  exact computable_equiv_of_matchings A B forward backward hforward hbackward hi hm hcF hcB hr

/-- Mathlib one-one equivalence of numerical predicates yields a computable
permutation, with computable inverse, carrying one predicate to the other. -/
theorem computable_permutation_of_oneOneEquiv (A B : Nat → Prop)
    (h : OneOneEquiv A B) :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ x, A x ↔ B (e x) := by
  obtain ⟨⟨f, hfc, hfi, hfr⟩, ⟨g, hgc, hgi, hgr⟩⟩ := h
  obtain ⟨u, v, huc, hvc, huv, hvu, hrel⟩ :=
    effective_isomorphism_of_oneOne A B f g hfc hgc hfi hgi hfr hgr
  let e : Nat ≃ Nat := ⟨u, v, huv, hvu⟩
  exact ⟨e, huc, hvc, hrel⟩

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
#print axioms edgeLookup_primrec
#print axioms edgeMatching_inverse
#print axioms edgeMatching_fresh
#print axioms extendLeft_spec
#print axioms extendRight_spec
#print axioms extendLeft_computable
#print axioms extendRight_computable
#print axioms matchingStages_computable
#print axioms matchingStages_valid
#print axioms matchingStages_mono
#print axioms effective_isomorphism_of_oneOne
#print axioms computable_permutation_of_oneOneEquiv
end LambdaTuring
