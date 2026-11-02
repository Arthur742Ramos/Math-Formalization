/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

Development checkpoint for closed-program finite numerical domains.
-/
module
public import LambdaTuring.TotalityBounded
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LambdaTuring

/-- Inputs on which the program has a full-beta Church-numeral observation. -/
def numericalDomain (t : Term) : Set Nat := {n | (numericalValue t n).Dom}

/-- The target predicate uses the actual finite numerical domain of a closed program. -/
def ClosedFiniteNumericalDomain (t : Term) : Prop :=
  Scoped 0 t ∧ (numericalDomain t).Finite

theorem finite_numericalDomain_iff_eventually_none (t : Term) :
    (numericalDomain t).Finite ↔ ∃ b, ∀ n, b ≤ n → ¬ (numericalValue t n).Dom := by
  classical
  constructor
  · intro hf
    refine ⟨hf.toFinset.sup id + 1, ?_⟩
    intro n hn hdom
    have hbound : n ≤ hf.toFinset.sup id :=
      Finset.le_sup (f := id) (hf.mem_toFinset.mpr hdom)
    omega
  · rintro ⟨b, hb⟩
    apply (Finset.finite_toSet (Finset.range b)).subset
    intro n hn
    change n ∈ Finset.range b
    apply Finset.mem_range.mpr
    by_contra hle
    exact hb n (by omega) hn

/-- A bounded check either concerns an input below the cutoff or observes no value. -/
def finiteDomainBoundedWitness (p : (Nat.Partrec.Code × Nat) × Nat) : Bool :=
  let nk := Nat.unpair p.2
  decide (nk.1 < p.1.2) || !boundedTotalityWitness ((p.1.1, nk.1), nk.2)

theorem finiteDomainBoundedWitness_primrec : Primrec finiteDomainBoundedWitness := by
  let P := (Nat.Partrec.Code × Nat) × Nat
  have hc : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have hnk : Primrec (fun p : P => Nat.unpair p.2) := Primrec.unpair.comp Primrec.snd
  have hn : Primrec (fun p : P => (Nat.unpair p.2).1) := Primrec.fst.comp hnk
  have hk : Primrec (fun p : P => (Nat.unpair p.2).2) := Primrec.snd.comp hnk
  have hcheck : Primrec (fun p : P => boundedTotalityWitness ((p.1.1, (Nat.unpair p.2).1),
      (Nat.unpair p.2).2)) :=
    boundedTotalityWitness_primrec.comp ((hc.pair hn).pair hk)
  exact Primrec.or.comp (Primrec.nat_lt.decide.comp hn hb) (Primrec.not.comp hcheck)

theorem code_no_domain_iff_bounded (c : Nat.Partrec.Code) (n : Nat) :
    ¬ (Nat.Partrec.Code.eval c n).Dom ↔
      ∀ k, boundedTotalityWitness ((c, n), k) = false := by
  constructor
  · intro h k
    cases he : boundedTotalityWitness ((c, n), k) with
    | false => rfl
    | true => exact False.elim (h ((eval_dom_iff_bounded c n).mpr ⟨k, he⟩))
  · intro h hd
    obtain ⟨k, hk⟩ := (eval_dom_iff_bounded c n).mp hd
    rw [h k] at hk
    contradiction

theorem code_eventually_no_domain_iff_bounded (c : Nat.Partrec.Code) :
    (∃ b, ∀ n, b ≤ n → ¬ (Nat.Partrec.Code.eval c n).Dom) ↔
      ∃ b, ∀ i, finiteDomainBoundedWitness ((c, b), i) = true := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro i
    by_cases hi : (Nat.unpair i).1 < b
    · simp [finiteDomainBoundedWitness, hi]
    · have hnone := (code_no_domain_iff_bounded c (Nat.unpair i).1).mp
        (hb (Nat.unpair i).1 (Nat.le_of_not_gt hi)) (Nat.unpair i).2
      simp [finiteDomainBoundedWitness, hi, hnone]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro n hn
    apply (code_no_domain_iff_bounded c n).mpr
    intro k
    have h := hb (Nat.pair n k)
    have hnot : ¬ n < b := Nat.not_lt_of_ge hn
    simpa [finiteDomainBoundedWitness, hnot] using h

/-- Open terms are sent to a total code, keeping the ambient predicate false. -/
def closedFiniteDomainCode (u : Nat.Partrec.Code) (t : Term) : Nat.Partrec.Code :=
  if requiredDepth t ≤ 0 then Nat.Partrec.Code.curry u (executableTermEncode t)
  else .zero

theorem closedFiniteDomainCode_primrec (u : Nat.Partrec.Code) :
    Primrec (closedFiniteDomainCode u) := by
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  unfold closedFiniteDomainCode
  exact Primrec.ite (Primrec.nat_le.comp primrec_requiredDepth (Primrec.const 0))
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) henc) (Primrec.const _)

theorem closedFiniteDomainCode_correct (u : Nat.Partrec.Code) (hu : UniformLambdaCode u)
    (t : Term) : ClosedFiniteNumericalDomain t ↔
      ∃ b, ∀ n, b ≤ n → ¬ (Nat.Partrec.Code.eval (closedFiniteDomainCode u t) n).Dom := by
  by_cases h : requiredDepth t ≤ 0
  · have hs : Scoped 0 t := (scoped_iff_requiredDepth_le t 0).mpr h
    have he (n : Nat) : Nat.Partrec.Code.eval (closedFiniteDomainCode u t) n =
        numericalValue t n := by
      simpa [closedFiniteDomainCode, h, Nat.Partrec.Code.eval_curry] using hu t n
    simp only [ClosedFiniteNumericalDomain, hs, true_and,
      finite_numericalDomain_iff_eventually_none, he]
  · have hs : ¬ Scoped 0 t := fun hs => h ((scoped_iff_requiredDepth_le t 0).mp hs)
    have hnot : ¬ ∃ b, ∀ n, b ≤ n →
        ¬ (Nat.Partrec.Code.eval (closedFiniteDomainCode u t) n).Dom := by
      rintro ⟨b, hb⟩
      have hzero := hb b (Nat.le_refl b)
      simp only [closedFiniteDomainCode, h, ↓reduceIte] at hzero
      exact hzero (by change (Part.some 0).Dom; trivial)
    simp [ClosedFiniteNumericalDomain, hs, hnot]

theorem closedFiniteNumericalDomain_has_bounded_form :
    ∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedFiniteNumericalDomain t ↔
        ∃ b, ∀ i, finiteDomainBoundedWitness ((f t, b), i) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  refine ⟨closedFiniteDomainCode u, closedFiniteDomainCode_primrec u, ?_⟩
  intro t
  exact (closedFiniteDomainCode_correct u hu t).trans (code_eventually_no_domain_iff_bounded _)

/-- A finite prefix of possible witnesses has been refuted. -/
def PrefixRefuted (R : (Nat × Nat) × Nat → Bool) (a n : Nat) : Prop :=
  ∀ i ≤ n, ∃ k, R ((a, i), k) = false

/-- Decide whether a counterexample has appeared by a fixed stage. -/
@[irreducible] def counterexampleBy (R : (Nat × Nat) × Nat → Bool) (a i s : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (!(R ((a, i), 0)))
    (fun k b => b || !(R ((a, i), k + 1))) s

@[simp] theorem counterexampleBy_zero (R : (Nat × Nat) × Nat → Bool) (a i : Nat) :
    counterexampleBy R a i 0 = !(R ((a, i), 0)) := by
  unfold counterexampleBy
  rfl

@[simp] theorem counterexampleBy_succ (R : (Nat × Nat) × Nat → Bool) (a i s : Nat) :
    counterexampleBy R a i (s + 1) =
      (counterexampleBy R a i s || !(R ((a, i), s + 1))) := by
  unfold counterexampleBy
  rfl

/-- Check the stage bound for every candidate in the finite input prefix. -/
@[irreducible] def prefixRefutedBy (R : (Nat × Nat) × Nat → Bool) (a s n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (counterexampleBy R a 0 s)
    (fun i b => b && counterexampleBy R a (i + 1) s) n

@[simp] theorem prefixRefutedBy_zero (R : (Nat × Nat) × Nat → Bool) (a s : Nat) :
    prefixRefutedBy R a s 0 = counterexampleBy R a 0 s := by
  unfold prefixRefutedBy
  rfl

@[simp] theorem prefixRefutedBy_succ (R : (Nat × Nat) × Nat → Bool) (a s n : Nat) :
    prefixRefutedBy R a s (n + 1) =
      (prefixRefutedBy R a s n && counterexampleBy R a (n + 1) s) := by
  unfold prefixRefutedBy
  rfl

/-- Search is partial exactly when the finite prefix has no common refutation stage. -/
def prefixSearch (R : (Nat × Nat) × Nat → Bool) (encoded : Nat) : Part Nat :=
  Nat.rfind (fun s => (prefixRefutedBy R (Nat.unpair encoded).1 s
    (Nat.unpair encoded).2 : Part Bool))

/-- Bounded counterexample search is computable when the underlying test is. -/
theorem counterexampleBy_computable (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Computable (fun p : (Nat × Nat) × Nat => counterexampleBy R p.1.1 p.1.2 p.2) := by
  let A := Nat × Nat
  let P := A × Nat
  let Q := P × (Nat × Bool)
  have hbase : Computable (fun p : P => !(R (p.1, 0))) :=
    Primrec.not.to_comp.comp (hR.comp (Computable.fst.pair (Computable.const 0)))
  have harg : Computable (fun q : Q => (q.1.1, q.2.1 + 1)) :=
    (Computable.fst.comp Computable.fst).pair
      (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
  have hnew : Computable (fun q : Q => !(R (q.1.1, q.2.1 + 1))) :=
    Primrec.not.to_comp.comp (hR.comp harg)
  have hold : Computable (fun q : Q => q.2.2) := Computable.snd.comp Computable.snd
  have hstep : Computable₂ (fun (p : P) (q : Nat × Bool) => q.2 || !(R (p.1, q.1 + 1))) :=
    (Primrec.or.to_comp.comp hold hnew).to₂
  have h := Computable.nat_rec Computable.snd hbase hstep
  apply h.of_eq
  rintro ⟨⟨a, i⟩, s⟩
  unfold counterexampleBy
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The first candidate in a bounded prefix has a computable stage test. -/
theorem prefixRefutedBy_base_computable (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Computable (fun p : (Nat × Nat) × Nat => counterexampleBy R p.1.1 0 p.1.2) := by
  let P := (Nat × Nat) × Nat
  have hc : Computable (fun p : (Nat × Nat) × Nat =>
      counterexampleBy R p.1.1 p.1.2 p.2) := counterexampleBy_computable R hR
  have ha : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have hs : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  exact hc.comp ((ha.pair (Computable.const 0)).pair hs)

abbrev PrefixStepInput := ((Nat × Nat) × Nat) × (Nat × Bool)

theorem prefixStepArg_primrec :
    Primrec (fun q : PrefixStepInput => ((q.1.1.1, q.2.1 + 1), q.1.1.2)) :=
  (((Primrec.fst.comp Primrec.fst).comp Primrec.fst).pair
    (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).pair
    ((Primrec.snd.comp Primrec.fst).comp Primrec.fst)

theorem prefixStepIndicator_computable (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Computable (fun q : PrefixStepInput =>
      counterexampleBy R q.1.1.1 (q.2.1 + 1) q.1.1.2) := by
  have hc : Computable (fun p : (Nat × Nat) × Nat =>
      counterexampleBy R p.1.1 p.1.2 p.2) := counterexampleBy_computable R hR
  have hp : Computable (fun q : PrefixStepInput =>
      ((q.1.1.1, q.2.1 + 1), q.1.1.2)) := prefixStepArg_primrec.to_comp
  have hcomp := Computable.comp
    (f := fun p : (Nat × Nat) × Nat => counterexampleBy R p.1.1 p.1.2 p.2)
    (g := fun q : PrefixStepInput => ((q.1.1.1, q.2.1 + 1), q.1.1.2)) hc hp
  refine hcomp.of_eq ?_
  intro q
  rfl

/-- Advancing one prefix candidate preserves computability. -/
theorem prefixRefutedBy_step_computable (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Computable₂ (fun (p : (Nat × Nat) × Nat) (q : Nat × Bool) =>
      q.2 && counterexampleBy R p.1.1 (q.1 + 1) p.1.2) := by
  change Computable (fun q : PrefixStepInput =>
    q.2.2 && counterexampleBy R q.1.1.1 (q.2.1 + 1) q.1.1.2)
  exact Primrec.and.to_comp.comp (Primrec.snd.comp Primrec.snd).to_comp
    (prefixStepIndicator_computable R hR)

/-- Uniform finite-prefix testing is computable, including the stage bound. -/
theorem prefixRefutedBy_computable (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Computable (fun p : (Nat × Nat) × Nat => prefixRefutedBy R p.1.1 p.1.2 p.2) := by
  let P := (Nat × Nat) × Nat
  have h : Computable (fun p : P => Nat.rec (motive := fun _ => Bool) (counterexampleBy R p.1.1 0 p.1.2)
      (fun n b => b && counterexampleBy R p.1.1 (n + 1) p.1.2) p.2) :=
    Computable.nat_rec (f := fun p : P => p.2)
      (g := fun p : P => counterexampleBy R p.1.1 0 p.1.2)
      (h := fun p : P => fun q : Nat × Bool =>
        q.2 && counterexampleBy R p.1.1 (q.1 + 1) p.1.2)
      Computable.snd (prefixRefutedBy_base_computable R hR) (prefixRefutedBy_step_computable R hR)
  apply h.of_eq
  rintro ⟨⟨a, s⟩, n⟩
  unfold prefixRefutedBy
  rfl

theorem prefixSearch_partrec (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    Nat.Partrec (prefixSearch R) := by
  have hdecode : Computable (fun p : Nat × Nat =>
      (((Nat.unpair p.1).1, p.2), (Nat.unpair p.1).2)) := by
    have hpair : Computable (fun p : Nat × Nat => Nat.unpair p.1) :=
      Computable.unpair.comp Computable.fst
    exact (((Computable.fst.comp hpair).pair Computable.snd).pair
      (Computable.snd.comp hpair))
  have hstage : Computable (fun p : Nat × Nat => prefixRefutedBy R
      (Nat.unpair p.1).1 p.2 (Nat.unpair p.1).2) :=
    (prefixRefutedBy_computable R hR).comp hdecode
  apply Partrec.nat_iff.1
  exact Partrec.rfind hstage.partrec.to₂

theorem counterexampleBy_iff (R : (Nat × Nat) × Nat → Bool) (a i s : Nat) :
    counterexampleBy R a i s = true ↔ ∃ k ≤ s, R ((a, i), k) = false := by
  induction s with
  | zero => simp [counterexampleBy_zero]
  | succ s ih =>
    constructor
    · intro h
      have hcases : counterexampleBy R a i s = true ∨ R ((a, i), s + 1) = false := by
        simpa [counterexampleBy_succ] using h
      rcases hcases with hp | hp
      · obtain ⟨k, hk, hr⟩ := ih.mp hp
        exact ⟨k, Nat.le_trans hk (Nat.le_succ s), hr⟩
      · exact ⟨s + 1, le_rfl, hp⟩
    · rintro ⟨k, hk, hr⟩
      by_cases hs : k ≤ s
      · have hp := ih.mpr ⟨k, hs, hr⟩
        simp [counterexampleBy_succ, hp]
      · have hk' : k = s + 1 := by omega
        subst k
        simp [counterexampleBy_succ, hr]

theorem prefixRefutedBy_iff (R : (Nat × Nat) × Nat → Bool) (a s n : Nat) :
    prefixRefutedBy R a s n = true ↔
      ∀ i ≤ n, ∃ k ≤ s, R ((a, i), k) = false := by
  induction n with
  | zero => simp [prefixRefutedBy_zero, counterexampleBy_iff]
  | succ n ih =>
    constructor
    · intro h
      have hp : prefixRefutedBy R a s n = true ∧
          counterexampleBy R a (n + 1) s = true := by
        simpa [prefixRefutedBy_succ] using h
      intro i hi
      by_cases hsmall : i ≤ n
      · exact ih.mp hp.1 i hsmall
      · have hi' : i = n + 1 := by omega
        subst i
        exact (counterexampleBy_iff R a (n + 1) s).mp hp.2
    · intro h
      have hp : prefixRefutedBy R a s n = true := ih.mpr
        (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))
      have hc : counterexampleBy R a (n + 1) s = true :=
        (counterexampleBy_iff R a (n + 1) s).mpr (h (n + 1) le_rfl)
      simp [prefixRefutedBy_succ, hp, hc]

/-- A finite family of counterexamples has one common stage bound. -/
theorem prefixRefuted_iff_bounded (R : (Nat × Nat) × Nat → Bool) (a n : Nat) :
    PrefixRefuted R a n ↔
      ∃ s, ∀ i ≤ n, ∃ k ≤ s, R ((a, i), k) = false := by
  constructor
  · induction n with
    | zero =>
      intro h
      obtain ⟨k, hk⟩ := h 0 (Nat.le_refl 0)
      refine ⟨k, ?_⟩
      intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact ⟨k, le_rfl, hk⟩
    | succ n ih =>
      intro h
      obtain ⟨s, hs⟩ := ih (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))
      obtain ⟨k, hk⟩ := h (n + 1) (Nat.le_refl _)
      refine ⟨max s k, ?_⟩
      intro i hi
      by_cases hsmall : i ≤ n
      · obtain ⟨j, hj, hR⟩ := hs i hsmall
        exact ⟨j, Nat.le_trans hj (le_max_left s k), hR⟩
      · have hi' : i = n + 1 := by omega
        subst i
        exact ⟨k, le_max_right s k, hk⟩
  · rintro ⟨s, hs⟩ i hi
    obtain ⟨k, _, hk⟩ := hs i hi
    exact ⟨k, hk⟩

set_option backward.isDefEq.respectTransparency false in
theorem prefixSearch_dom_iff (R : (Nat × Nat) × Nat → Bool) (a n : Nat) :
    (prefixSearch R (Nat.pair a n)).Dom ↔ PrefixRefuted R a n := by
  constructor
  · intro h
    rw [prefixSearch, Nat.unpair_pair, Nat.rfind_dom] at h
    obtain ⟨s, hs, _⟩ := h
    apply (prefixRefuted_iff_bounded R a n).mpr
    exact ⟨s, (prefixRefutedBy_iff R a s n).mp (by simpa using hs)⟩
  · intro h
    obtain ⟨s, hs⟩ := (prefixRefuted_iff_bounded R a n).mp h
    rw [prefixSearch, Nat.unpair_pair, Nat.rfind_dom]
    refine ⟨s, ?_, fun {_} _ => trivial⟩
    simpa using (prefixRefutedBy_iff R a s n).mpr hs

/-- The construction has a finite-domain/total-domain gap. -/
theorem prefixRefuted_eventually_false_iff (R : (Nat × Nat) × Nat → Bool) (a : Nat) :
    (∃ i, ∀ k, R ((a, i), k) = true) ↔
      ∃ b, ∀ n, b ≤ n → ¬ PrefixRefuted R a n := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro n hn hp
    obtain ⟨k, hk⟩ := hp i hn
    have := hi k
    simp_all
  · rintro ⟨b, hb⟩
    by_contra hgood
    have hbad (i : Nat) : ∃ k, R ((a, i), k) = false := by
      by_contra h
      apply hgood
      refine ⟨i, ?_⟩
      intro k
      cases he : R ((a, i), k) with
      | false => exact False.elim (h ⟨k, he⟩)
      | true => rfl
    exact hb b (Nat.le_refl b) (fun i _ => hbad i)

/-- If the Σ₂ predicate fails, every natural input enters the constructed domain. -/
theorem prefixRefuted_all_of_no_witness (R : (Nat × Nat) × Nat → Bool) (a : Nat)
    (h : ¬ ∃ i, ∀ k, R ((a, i), k) = true) : ∀ n, PrefixRefuted R a n := by
  classical
  intro n i _
  by_contra hbad
  apply h
  refine ⟨i, ?_⟩
  intro k
  cases he : R ((a, i), k) with
  | false => exact False.elim (hbad ⟨k, he⟩)
  | true => rfl

/-- A least successful candidate cuts the prefix-refutation domain exactly there. -/
theorem prefixRefuted_iff_lt_least (R : (Nat × Nat) × Nat → Bool) (a m : Nat)
    (hgood : ∀ k, R ((a, m), k) = true)
    (hleast : ∀ i, i < m → ¬ ∀ k, R ((a, i), k) = true) (n : Nat) :
    PrefixRefuted R a n ↔ n < m := by
  classical
  constructor
  · intro h
    by_contra hn
    have hm : m ≤ n := by omega
    obtain ⟨k, hk⟩ := h m hm
    have := hgood k
    simp_all
  · intro hn i hi
    have hnot := hleast i (Nat.lt_of_le_of_lt hi hn)
    by_contra hbad
    apply hnot
    intro k
    cases he : R ((a, i), k) with
    | false => exact False.elim (hbad ⟨k, he⟩)
    | true => rfl

/-- The code parameter is fixed once for the given computable relation. -/
def finiteDomainCompiler (u : Nat.Partrec.Code) (a : Nat) : Term :=
  compileLambdaTotal (Nat.Partrec.Code.curry u a)

theorem finiteDomainCompiler_primrec (u : Nat.Partrec.Code) :
    Primrec (finiteDomainCompiler u) :=
  primrec_compileLambdaTotal.comp
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id)

theorem finiteDomainCompiler_dom (R : (Nat × Nat) × Nat → Bool)
    (u : Nat.Partrec.Code) (hu : ∀ z, Nat.Partrec.Code.eval u z = prefixSearch R z)
    (a n : Nat) :
    (numericalValue (finiteDomainCompiler u a) n).Dom ↔ PrefixRefuted R a n := by
  rw [finiteDomainCompiler, (compileLambdaTotal_sound _).2 n,
    Nat.Partrec.Code.eval_curry, hu, prefixSearch_dom_iff]

theorem finiteDomainCompiler_correct (R : (Nat × Nat) × Nat → Bool)
    (u : Nat.Partrec.Code) (hu : ∀ z, Nat.Partrec.Code.eval u z = prefixSearch R z)
    (a : Nat) :
    ((∃ i, ∀ k, R ((a, i), k) = true) ↔
      ClosedFiniteNumericalDomain (finiteDomainCompiler u a)) ∧
    (¬ (∃ i, ∀ k, R ((a, i), k) = true) →
      ClosedNumericalTotal (finiteDomainCompiler u a)) := by
  have hdom := finiteDomainCompiler_dom R u hu a
  constructor
  · constructor
    · intro h
      obtain ⟨b, hb⟩ := (prefixRefuted_eventually_false_iff R a).mp h
      refine ⟨(compileLambdaTotal_sound _).1,
        (finite_numericalDomain_iff_eventually_none _).mpr ⟨b, ?_⟩⟩
      intro n hn hd
      exact hb n hn ((hdom n).mp hd)
    · intro h
      obtain ⟨b, hb⟩ := (finite_numericalDomain_iff_eventually_none _).mp h.2
      apply (prefixRefuted_eventually_false_iff R a).mpr
      refine ⟨b, ?_⟩
      intro n hn hp
      exact hb n hn ((hdom n).mpr hp)
  · intro h
    refine ⟨(compileLambdaTotal_sound _).1, ?_⟩
    intro n
    exact (hdom n).mpr (prefixRefuted_all_of_no_witness R a h n)

/-- A successful candidate yields exactly the initial segment below the least one. -/
theorem finiteDomainCompiler_exact_initial_segment (R : (Nat × Nat) × Nat → Bool)
    (u : Nat.Partrec.Code) (hu : ∀ z, Nat.Partrec.Code.eval u z = prefixSearch R z)
    (a : Nat) (hgood : ∃ i, ∀ k, R ((a, i), k) = true) :
    ∃ m, (∀ k, R ((a, m), k) = true) ∧
      (∀ i, i < m → ¬ ∀ k, R ((a, i), k) = true) ∧
      ∀ n, (numericalValue (finiteDomainCompiler u a) n).Dom ↔ n < m := by
  classical
  refine ⟨Nat.find hgood, Nat.find_spec hgood, ?_, ?_⟩
  · intro i hi
    exact Nat.find_min hgood hi
  · intro n
    exact (finiteDomainCompiler_dom R u hu a n).trans
      (prefixRefuted_iff_lt_least R a (Nat.find hgood)
        (Nat.find_spec hgood) (fun i hi => Nat.find_min hgood hi) n)

/-- Candidate Σ₂ hardness theorem with a finite-domain/total-domain gap. -/
theorem closedFiniteNumericalDomain_normalForm_hard
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ∃ f : Nat → Term, Primrec f ∧ ∀ a,
      ((∃ i, ∀ k, R ((a, i), k) = true) ↔ ClosedFiniteNumericalDomain (f a)) ∧
      (¬ (∃ i, ∀ k, R ((a, i), k) = true) → ClosedNumericalTotal (f a)) := by
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (prefixSearch_partrec R hR)
  exact ⟨finiteDomainCompiler u, finiteDomainCompiler_primrec u,
    finiteDomainCompiler_correct R u (congrFun hu)⟩

/-- The reduction produces a precise initial segment, or else a total domain. -/
theorem closedFiniteNumericalDomain_normalForm_exact_gap
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ∃ f : Nat → Term, Primrec f ∧
      (∀ a, (∃ i, ∀ k, R ((a, i), k) = true) →
        ∃ m, (∀ k, R ((a, m), k) = true) ∧
          (∀ i, i < m → ¬ ∀ k, R ((a, i), k) = true) ∧
          ∀ n, (numericalValue (f a) n).Dom ↔ n < m) ∧
      (∀ a, ¬ (∃ i, ∀ k, R ((a, i), k) = true) → ClosedNumericalTotal (f a)) := by
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (prefixSearch_partrec R hR)
  refine ⟨finiteDomainCompiler u, finiteDomainCompiler_primrec u, ?_, ?_⟩
  · intro a hgood
    exact finiteDomainCompiler_exact_initial_segment R u (congrFun hu) a hgood
  · intro a hbad
    exact (finiteDomainCompiler_correct R u (congrFun hu) a).2 hbad

/-- Candidate Σ₂ normal-form completeness, over all syntactic terms. -/
theorem closedFiniteNumericalDomain_normalForm_complete :
    Primrec finiteDomainBoundedWitness ∧
    (∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedFiniteNumericalDomain t ↔
        ∃ b, ∀ i, finiteDomainBoundedWitness ((f t, b), i) = true)) ∧
    ∀ R : (Nat × Nat) × Nat → Bool, Computable R →
      ManyOneReducible (fun a => ∃ i, ∀ k, R ((a, i), k) = true)
        ClosedFiniteNumericalDomain := by
  refine ⟨finiteDomainBoundedWitness_primrec,
    closedFiniteNumericalDomain_has_bounded_form, ?_⟩
  intro R hR
  obtain ⟨f, hf, hcorrect⟩ := closedFiniteNumericalDomain_normalForm_hard R hR
  exact ⟨f, hf.to_comp, fun a => (hcorrect a).1⟩

#print axioms closedFiniteNumericalDomain_normalForm_complete
#print axioms closedFiniteNumericalDomain_normalForm_exact_gap
#print axioms prefixSearch_partrec
#print axioms finiteDomainBoundedWitness_primrec

end LambdaTuring
