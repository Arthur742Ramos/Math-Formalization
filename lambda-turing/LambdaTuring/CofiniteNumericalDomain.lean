/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

Working increment: cofinite numerical domains of closed lambda programs.
-/
module
public import LambdaTuring.TotalityBounded
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LambdaTuring

/-- Inputs with no reachable numerical result after application to a numeral.
This includes nonnumerical normal forms and is not a divergence predicate. -/
def missingNumericalDomain (t : Term) : Set Nat :=
  {n | ¬ (numericalValue t n).Dom}

def ClosedCofiniteNumericalDomain (t : Term) : Prop :=
  Scoped 0 t ∧ (missingNumericalDomain t).Finite

theorem finite_missing_iff_eventually_defined (t : Term) :
    (missingNumericalDomain t).Finite ↔
      ∃ b, ∀ n, b ≤ n → (numericalValue t n).Dom := by
  classical
  constructor
  · intro hf
    refine ⟨hf.toFinset.sup id + 1, ?_⟩
    intro n hn
    by_contra hdom
    have hbound : n ≤ hf.toFinset.sup id :=
      Finset.le_sup (f := id) (hf.mem_toFinset.mpr hdom)
    omega
  · rintro ⟨b, hb⟩
    apply (Finset.finite_toSet (Finset.range b)).subset
    intro n hn
    change n ∈ Finset.range b
    apply Finset.mem_range.mpr
    by_contra hle
    exact hn (hb n (by omega))

def CodeCofinite (c : Nat.Partrec.Code) : Prop :=
  ∃ b, ∀ n, b ≤ n → (Nat.Partrec.Code.eval c n).Dom

theorem closedCofiniteCode_correct (u : Nat.Partrec.Code) (hu : UniformLambdaCode u)
    (t : Term) : ClosedCofiniteNumericalDomain t ↔ CodeCofinite (closedTotalityCode u t) := by
  by_cases h : requiredDepth t ≤ 0
  · have hs : Scoped 0 t := (scoped_iff_requiredDepth_le t 0).2 h
    have he (n : Nat) : Nat.Partrec.Code.eval (closedTotalityCode u t) n = numericalValue t n := by
      simp only [closedTotalityCode, h, ↓reduceIte, Nat.Partrec.Code.eval_curry]
      exact hu t n
    simp only [ClosedCofiniteNumericalDomain, CodeCofinite, hs, true_and,
      finite_missing_iff_eventually_defined, he]
  · have hs : ¬ Scoped 0 t := fun hs => h ((scoped_iff_requiredDepth_le t 0).1 hs)
    have hnot : ¬ CodeCofinite (closedTotalityCode u t) := by
      rintro ⟨b, hb⟩
      have hzero := hb b (Nat.le_refl b)
      simp only [closedTotalityCode, h, ↓reduceIte, bottomCode_eval] at hzero
      exact hzero
    simp [ClosedCofiniteNumericalDomain, hs, hnot]

/-- A primitive-recursive test for the universal-existential portion of the
cofinite normal form. -/
def cofiniteBoundedWitness (p : ((Nat.Partrec.Code × Nat) × Nat) × Nat) : Bool :=
  decide (p.1.2 < p.1.1.2) || boundedTotalityWitness ((p.1.1.1, p.1.2), p.2)

theorem cofiniteBoundedWitness_primrec : Primrec cofiniteBoundedWitness := by
  let P := ((Nat.Partrec.Code × Nat) × Nat) × Nat
  have hc : Primrec (fun p : P => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec (fun p : P => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun p : P => p.2) := Primrec.snd
  have hcheck : Primrec (fun p : P => boundedTotalityWitness ((p.1.1.1, p.1.2), p.2)) :=
    boundedTotalityWitness_primrec.comp ((hc.pair hn).pair hk)
  exact Primrec.or.comp (Primrec.nat_lt.decide.comp hn hb) hcheck

theorem codeCofinite_iff_bounded (c : Nat.Partrec.Code) :
    CodeCofinite c ↔ ∃ b, ∀ n, ∃ k, cofiniteBoundedWitness (((c, b), n), k) = true := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro n
    by_cases h : n < b
    · exact ⟨0, by simp [cofiniteBoundedWitness, h]⟩
    · obtain ⟨k, hk⟩ := (eval_dom_iff_bounded c n).1 (hb n (Nat.le_of_not_gt h))
      exact ⟨k, by simp [cofiniteBoundedWitness, h, hk]⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨k, hk⟩ := hb n
    have hnot : ¬ n < b := Nat.not_lt_of_ge hn
    apply (eval_dom_iff_bounded c n).2
    exact ⟨k, by simpa [cofiniteBoundedWitness, hnot] using hk⟩

theorem closedCofinite_has_bounded_form :
    ∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedCofiniteNumericalDomain t ↔
        ∃ b, ∀ n, ∃ k, cofiniteBoundedWitness (((f t, b), n), k) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  exact ⟨closedTotalityCode u, closedTotalityCode_primrec u,
    fun t => (closedCofiniteCode_correct u hu t).trans (codeCofinite_iff_bounded _)⟩

/-- The marker for a level survives at a stage exactly when that stage is
the last event at that level. -/
def markerHoles (E : Nat → Nat → Prop) : Set (Nat × Nat) :=
  {p | E p.1 p.2 ∧ ∀ t, p.2 < t → ¬ E p.1 t}

def InfinitelyOften (p : Nat → Prop) : Prop := ∀ s, ∃ t, s < t ∧ p t

/-- A monotone natural-valued approximation is unbounded precisely when it
strictly increases at arbitrarily late stages. -/
theorem monotone_unbounded_iff_late_increases (f : Nat → Nat) (hf : Monotone f) :
    (∀ b, ∃ s, b < f s) ↔ ∀ m, ∃ s, m ≤ s ∧ f s < f (s + 1) := by
  constructor
  · intro hunbounded m
    by_contra h
    have hstep : ∀ s, m ≤ s → f (s + 1) ≤ f s := by
      intro s hs
      by_contra hlt
      exact h ⟨s, hs, Nat.lt_of_not_ge hlt⟩
    have htail : ∀ k, f (m + k) ≤ f m := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hs := hstep (m + k) (by omega)
        exact le_trans (by simpa [Nat.add_assoc] using hs) ih
    have hbound : ∀ s, f s ≤ f m := by
      intro s
      by_cases hs : s ≤ m
      · exact hf hs
      · have ht := htail (s - m)
        have he : m + (s - m) = s := by omega
        simpa [he] using ht
    obtain ⟨s, hs⟩ := hunbounded (f m)
    exact (Nat.not_lt_of_ge (hbound s)) hs
  · intro hinc b
    have hgrowth : ∀ k, ∃ s, k ≤ f s := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨s, hs⟩ := ih
        obtain ⟨t, hst, ht⟩ := hinc s
        refine ⟨t + 1, ?_⟩
        have hm := hf hst
        omega
    obtain ⟨s, hs⟩ := hgrowth (b + 1)
    exact ⟨s, by omega⟩

theorem markerHoles_fst_injective (E : Nat → Nat → Prop) :
    Set.InjOn Prod.fst (markerHoles E) := by
  rintro ⟨i, s⟩ hs ⟨j, t⟩ ht heq
  change i = j at heq
  subst j
  have he : s = t := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hs.2 t hlt ht.1
    · exact ht.2 s hgt hs.1
  subst t
  rfl

/-- The last event exists if an event occurs at zero and the events stop. -/
theorem markerHoles_exists_of_not_infinite (E : Nat → Nat → Prop) (i : Nat)
    (hzero : E i 0) (hnot : ¬ InfinitelyOften (E i)) :
    ∃ s, (i, s) ∈ markerHoles E := by
  classical
  simp only [InfinitelyOften, not_forall, not_exists, not_and] at hnot
  obtain ⟨b, hb⟩ := hnot
  let S := (Finset.range (b + 1)).filter (E i)
  have hS : S.Nonempty := ⟨0, by simp [S, hzero]⟩
  let s := S.max' hS
  have hs : s ∈ S := Finset.max'_mem S hS
  have he : E i s := (Finset.mem_filter.1 hs).2
  refine ⟨s, he, ?_⟩
  intro t hst ht
  by_cases htb : t ≤ b
  · have htS : t ∈ S := by
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_range.2 (by omega), ht⟩
    have hts : t ≤ s := Finset.le_max' S t htS
    omega
  · exact hb t (by omega) ht

/-- Finite-injury marker principle: if higher levels inherit events and
all levels start with an event, only finitely many final markers exist
exactly when one level has infinitely many events. -/
theorem finite_marker_holes_iff (E : Nat → Nat → Prop)
    (hzero : ∀ i, E i 0)
    (hmono : ∀ i j s, i ≤ j → E i s → E j s) :
    (markerHoles E).Finite ↔ ∃ i, InfinitelyOften (E i) := by
  classical
  constructor
  · intro hfinite
    by_contra hnone
    have hall : ∀ i, ¬ InfinitelyOften (E i) := by
      intro i hi
      exact hnone ⟨i, hi⟩
    have hf : ((Prod.fst : Nat × Nat → Nat) '' markerHoles E).Finite :=
      hfinite.image Prod.fst
    have hu : (Set.univ : Set Nat) ⊆ Prod.fst '' markerHoles E := by
      intro i _
      obtain ⟨s, hs⟩ := markerHoles_exists_of_not_infinite E i (hzero i) (hall i)
      exact ⟨(i, s), hs, rfl⟩
    exact Set.infinite_univ (hf.subset hu)
  · rintro ⟨i, hi⟩
    have hf : ((Prod.fst : Nat × Nat → Nat) '' markerHoles E).Finite := by
      apply (Finset.finite_toSet (Finset.range i)).subset
      rintro j ⟨⟨k, s⟩, hk, rfl⟩
      change k ∈ Finset.range i
      apply Finset.mem_range.2
      by_contra hki
      obtain ⟨t, hst, ht⟩ := hi s
      exact hk.2 t hst (hmono i k t (Nat.le_of_not_gt hki) ht)
    exact hf.of_finite_image (markerHoles_fst_injective E)

/-- Number-coded domain: a code is present unless it names a last event. -/
def markerDomain (E : Nat → Nat → Prop) (n : Nat) : Prop :=
  Nat.unpair n ∉ markerHoles E

theorem markerDomain_cofinite_iff (E : Nat → Nat → Prop)
    (hzero : ∀ i, E i 0)
    (hmono : ∀ i j s, i ≤ j → E i s → E j s) :
    {n | ¬ markerDomain E n}.Finite ↔ ∃ i, InfinitelyOften (E i) := by
  have hset : {n | ¬ markerDomain E n} =
      (fun p : Nat × Nat => Nat.pair p.1 p.2) '' markerHoles E := by
    ext n
    constructor
    · intro hn
      have hh : Nat.unpair n ∈ markerHoles E := by simpa [markerDomain] using hn
      exact ⟨Nat.unpair n, hh, Nat.pair_unpair n⟩
    · rintro ⟨⟨i, s⟩, hp, rfl⟩
      simpa [markerDomain, Nat.unpair_pair] using hp
  have hinj : Function.Injective (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
    intro p q he
    have h := congrArg Nat.unpair he
    simpa [Nat.unpair_pair] using h
  rw [hset, Set.finite_image_iff hinj.injOn]
  exact finite_marker_holes_iff E hzero hmono

/-- A level receives an event at zero and whenever a lower-or-equal
approximation strictly increases. -/
def familyEvent (levels : Nat → Nat → Nat) (i s : Nat) : Prop :=
  s = 0 ∨ ∃ j ≤ i, ∃ k, s = k + 1 ∧ levels j k < levels j (k + 1)

theorem familyEvent_mono (levels : Nat → Nat → Nat) :
    ∀ i j s, i ≤ j → familyEvent levels i s → familyEvent levels j s := by
  intro i j s hij h
  rcases h with h | ⟨k, hki, n, hn, hinc⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, le_trans hki hij, n, hn, hinc⟩

/-- A finite family produces arbitrarily late events iff one member has an
unbounded monotone approximation. -/
theorem familyEvent_infinite_iff (levels : Nat → Nat → Nat)
    (hmono : ∀ j, Monotone (levels j)) :
    (∃ i, InfinitelyOften (familyEvent levels i)) ↔
      ∃ j, ∀ b, ∃ s, b < levels j s := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    by_contra hnone
    have hno (j : Nat) : ¬ ∀ b, ∃ s, b < levels j s :=
      fun h => hnone ⟨j, h⟩
    have hstab (j : Nat) : ∃ m, ∀ s, m ≤ s → ¬ levels j s < levels j (s + 1) := by
      have hn : ¬ ∀ m, ∃ s, m ≤ s ∧ levels j s < levels j (s + 1) :=
        fun h => hno j ((monotone_unbounded_iff_late_increases _ (hmono j)).2 h)
      push Not at hn
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, fun s hs => Nat.not_lt_of_ge (hm s hs)⟩
    let bounds : Nat → Nat := fun j => Classical.choose (hstab j)
    let M := (Finset.range (i + 1)).sup bounds
    obtain ⟨t, htM, ht⟩ := hi M
    rcases ht with ht | ⟨j, hji, k, htk, hinc⟩
    · omega
    · have hj : j ∈ Finset.range (i + 1) := Finset.mem_range.2 (by omega)
      have hjM : bounds j ≤ M := Finset.le_sup (f := bounds) hj
      have hbound : bounds j ≤ k := by omega
      exact Classical.choose_spec (hstab j) k hbound hinc
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    intro m
    obtain ⟨s, hs, hinc⟩ := (monotone_unbounded_iff_late_increases _ (hmono j)).1 hj m
    exact ⟨s + 1, by omega, Or.inr ⟨j, Nat.le_refl _, s, rfl, hinc⟩⟩

theorem familyMarker_cofinite_iff_unbounded (levels : Nat → Nat → Nat)
    (hmono : ∀ j, Monotone (levels j)) :
    {n | ¬ markerDomain (familyEvent levels) n}.Finite ↔
      ∃ j, ∀ b, ∃ s, b < levels j s := by
  rw [markerDomain_cofinite_iff (familyEvent levels) (fun _ => Or.inl rfl)
    (familyEvent_mono levels)]
  exact familyEvent_infinite_iff levels hmono

/-- At stage `s`, all requirements below `m` for candidate `i` have a
witness no larger than `s`. -/
def candidateCovered (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a i s m : Nat) : Prop :=
  ((List.range m).all fun j =>
    (List.range (s + 1)).any fun k => R (((a, i), j), k)) = true

instance (R : ((Nat × Nat) × Nat) × Nat → Bool) (a i s : Nat) :
    DecidablePred (candidateCovered R a i s) := fun _ => by
  unfold candidateCovered
  infer_instance

theorem candidateCovered_iff (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a i s m : Nat) : candidateCovered R a i s m ↔
      ∀ j < m, ∃ k ≤ s, R (((a, i), j), k) = true := by
  simp [candidateCovered, Nat.lt_succ_iff]

abbrev CandidateInput := ((Nat × Nat) × Nat) × Nat

/-- The bounded coverage test is primitive recursive when its underlying
four-argument Boolean predicate is primitive recursive. -/
theorem candidateCovered_primrec (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Primrec R) :
    PrimrecPred (fun p : CandidateInput => candidateCovered R p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let P := CandidateInput × Nat
  let Q := Nat × P
  have hai : Primrec (fun q : Q => q.2.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hj : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun q : Q => q.1) := Primrec.fst
  have hrel : PrimrecRel (fun (k : Nat) (p : P) => R ((p.1.1.1, p.2), k) = true) :=
    Primrec.eq.comp (hR.comp ((hai.pair hj).pair hk)) (Primrec.const true)
  have hks : Primrec (fun p : P => List.range (p.1.1.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hex : PrimrecPred (fun p : P =>
      ∃ k ∈ List.range (p.1.1.2 + 1), R ((p.1.1.1, p.2), k) = true) :=
    hrel.exists_mem_list.comp hks Primrec.id
  have hexRel : PrimrecRel (fun (j : Nat) (p : CandidateInput) =>
      ∃ k ∈ List.range (p.1.2 + 1), R ((p.1.1, j), k) = true) :=
    hex.comp (Primrec.snd.pair Primrec.fst)
  have hjs : Primrec (fun p : CandidateInput => List.range p.2) :=
    Primrec.list_range.comp Primrec.snd
  have hall := hexRel.forall_mem_list.comp hjs Primrec.id
  apply hall.of_eq
  intro p
  simp [candidateCovered_iff, Nat.lt_succ_iff]

/-- The largest covered prefix visible at a finite stage. -/
def candidateLevel (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a i s : Nat) : Nat :=
  Nat.findGreatest (candidateCovered R a i s) s

theorem candidateLevel_primrec (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Primrec R) :
    Primrec (fun p : (Nat × Nat) × Nat => candidateLevel R p.1.1 p.1.2 p.2) := by
  exact Primrec.nat_findGreatest Primrec.snd (candidateCovered_primrec R hR)

/-- The finite-injury event relation is primitive recursive for a primitive
recursive bounded predicate. -/
theorem candidateEvent_primrec (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Primrec R) :
    PrimrecPred (fun p : (Nat × Nat) × Nat =>
      familyEvent (fun i s => candidateLevel R p.1.1 i s) p.1.2 p.2) := by
  let P := (Nat × Nat) × Nat
  let Q := Nat × P
  have ha : Primrec (fun q : Q => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hj : Primrec (fun q : Q => q.1) := Primrec.fst
  have hs : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp Primrec.snd
  have hl : Primrec (fun q : Q => candidateLevel R q.2.1.1 q.1 (q.2.2 - 1)) :=
    (candidateLevel_primrec R hR).comp ((ha.pair hj).pair (Primrec.pred.comp hs))
  have hr : Primrec (fun q : Q => candidateLevel R q.2.1.1 q.1 q.2.2) :=
    (candidateLevel_primrec R hR).comp ((ha.pair hj).pair hs)
  have hrel : PrimrecRel (fun (j : Nat) (p : P) =>
      candidateLevel R p.1.1 j (p.2 - 1) < candidateLevel R p.1.1 j p.2) :=
    Primrec.nat_lt.comp hl hr
  have hlist : Primrec (fun p : P => List.range (p.1.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  have hex := hrel.exists_mem_list.comp hlist Primrec.id
  have hzero : PrimrecPred (fun p : P => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcombined := hzero.or hex
  apply hcombined.of_eq
  rintro ⟨⟨a, i⟩, s⟩
  simp only [List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (h | ⟨j, hji, hinc⟩)
    · exact Or.inl h
    · by_cases hs : s = 0
      · exact Or.inl hs
      · refine Or.inr ⟨j, hji, s - 1, by omega, ?_⟩
        have he : s - 1 + 1 = s := by omega
        simpa [he] using hinc
  · rintro (h | ⟨j, hji, k, rfl, hinc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hji, by simpa using hinc⟩

theorem candidateLevel_mono (R : ((Nat × Nat) × Nat) × Nat → Bool) (a i : Nat) :
    Monotone (candidateLevel R a i) := by
  intro s t hst
  unfold candidateLevel
  apply Nat.findGreatest_mono
  · intro m hm
    apply (candidateCovered_iff R a i t m).2
    intro j hj
    obtain ⟨k, hks, hk⟩ := (candidateCovered_iff R a i s m).1 hm j hj
    exact ⟨k, le_trans hks hst, hk⟩
  · exact hst

theorem candidateLevel_covered (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a i s : Nat) : candidateCovered R a i s (candidateLevel R a i s) := by
  unfold candidateLevel
  apply Nat.findGreatest_spec (m := 0) (by omega)
  simp [candidateCovered_iff]

/-- The visible prefix is unbounded exactly for a candidate satisfying all
of its existential requirements. -/
theorem candidateLevel_unbounded_iff (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a i : Nat) :
    (∀ b, ∃ s, b < candidateLevel R a i s) ↔
      ∀ j, ∃ k, R (((a, i), j), k) = true := by
  classical
  constructor
  · intro hunbounded j
    obtain ⟨s, hs⟩ := hunbounded j
    obtain ⟨k, _, hk⟩ := (candidateCovered_iff R a i s _).1 (candidateLevel_covered R a i s) j hs
    exact ⟨k, hk⟩
  · intro hgood b
    choose w hw using hgood
    let s := max (b + 1) ((Finset.range (b + 1)).sup w)
    have hbs : b + 1 ≤ s := le_max_left _ _
    have hcover : candidateCovered R a i s (b + 1) := by
      apply (candidateCovered_iff R a i s _).2
      intro j hj
      have hjs : w j ≤ (Finset.range (b + 1)).sup w :=
        Finset.le_sup (f := w) (Finset.mem_range.2 hj)
      exact ⟨w j, le_trans hjs (le_max_right _ _), hw j⟩
    have hlevel : b + 1 ≤ candidateLevel R a i s :=
      Nat.le_findGreatest hbs hcover
    exact ⟨s, by omega⟩

/-- The abstract marker domain realizes the intended existential-universal-
existential predicate; effectiveness of this domain is a further obligation. -/
theorem candidateMarker_cofinite_iff (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (a : Nat) :
    {n | ¬ markerDomain (familyEvent (fun i s => candidateLevel R a i s)) n}.Finite ↔
      ∃ i, ∀ j, ∃ k, R (((a, i), j), k) = true := by
  rw [familyMarker_cofinite_iff_unbounded _ (candidateLevel_mono R a)]
  exact exists_congr (candidateLevel_unbounded_iff R a)

/-- At a finite stage, release a marker if it was never an event or if a
later event has appeared. Successful observations carry only zero. -/
def markerStage (test : (Nat × Nat) × Nat → Bool) (p : (Nat × Nat) × Nat) : Option Nat :=
  let i := (Nat.unpair p.1.2).1
  let s := (Nat.unpair p.1.2).2
  let released := !test ((p.1.1, i), s) || test ((p.1.1, i), s + p.2 + 1)
  bif released then some 0 else none

theorem markerStage_primrec (test : (Nat × Nat) × Nat → Bool) (htest : Primrec test) :
    Primrec (markerStage test) := by
  let P := (Nat × Nat) × Nat
  have ha : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have hun : Primrec (fun p : P => Nat.unpair p.1.2) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun p : P => (Nat.unpair p.1.2).1) := Primrec.fst.comp hun
  have hs : Primrec (fun p : P => (Nat.unpair p.1.2).2) := Primrec.snd.comp hun
  have hk : Primrec (fun p : P => p.2) := Primrec.snd
  have hcurr : Primrec (fun p : P => test ((p.1.1, (Nat.unpair p.1.2).1),
      (Nat.unpair p.1.2).2)) := htest.comp ((ha.pair hi).pair hs)
  have hfuture : Primrec (fun p : P => test ((p.1.1, (Nat.unpair p.1.2).1),
      (Nat.unpair p.1.2).2 + p.2 + 1)) :=
    htest.comp ((ha.pair hi).pair (Primrec.succ.comp (Primrec.nat_add.comp hs hk)))
  exact Primrec.cond (Primrec.or.comp (Primrec.not.comp hcurr) hfuture)
    (Primrec.const (some 0)) (Primrec.const none)

noncomputable def markerSearch (test : (Nat × Nat) × Nat → Bool)
    (p : Nat × Nat) : Part Nat := Nat.rfindOpt fun k => markerStage test (p, k)

theorem markerSearch_partrec (test : (Nat × Nat) × Nat → Bool) (htest : Primrec test) :
    Partrec (markerSearch test) :=
  Partrec.rfindOpt (markerStage_primrec test htest).to_comp

theorem markerSearch_dom_iff (test : (Nat × Nat) × Nat → Bool) (a n : Nat) :
    (markerSearch test (a, n)).Dom ↔
      test ((a, (Nat.unpair n).1), (Nat.unpair n).2) = false ∨
        ∃ t, (Nat.unpair n).2 < t ∧ test ((a, (Nat.unpair n).1), t) = true := by
  rw [markerSearch, Nat.rfindOpt_dom]
  cases hc : test ((a, (Nat.unpair n).1), (Nat.unpair n).2) with
  | false =>
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact ⟨0, 0, by simp [markerStage, hc]⟩
  | true =>
    constructor
    · rintro ⟨k, y, hy⟩
      have ht : test ((a, (Nat.unpair n).1), (Nat.unpair n).2 + k + 1) = true := by
        cases he : test ((a, (Nat.unpair n).1), (Nat.unpair n).2 + k + 1) <;>
          simp [markerStage, hc, he] at hy ⊢
      exact Or.inr ⟨(Nat.unpair n).2 + k + 1, by omega, ht⟩
    · rintro (hfalse | ⟨t, ht, he⟩)
      · simp at hfalse
      · let k := t - (Nat.unpair n).2 - 1
        have hk : (Nat.unpair n).2 + k + 1 = t := by dsimp [k]; omega
        refine ⟨k, 0, ?_⟩
        simp [markerStage, hc, hk, he]

theorem markerSearch_only_zero (test : (Nat × Nat) × Nat → Bool) (a n y : Nat)
    (hy : y ∈ markerSearch test (a, n)) : y = 0 := by
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
  change y ∈ (bif !test ((a, (Nat.unpair n).1), (Nat.unpair n).2) ||
    test ((a, (Nat.unpair n).1), (Nat.unpair n).2 + k + 1) then some 0 else none) at hk
  cases h : (!test ((a, (Nat.unpair n).1), (Nat.unpair n).2) ||
    test ((a, (Nat.unpair n).1), (Nat.unpair n).2 + k + 1)) <;> simp_all

/-- The candidate marker domain has a uniform partial-recursive realization
when the underlying predicate is primitive recursive. -/
theorem candidateMarker_partrec (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Primrec R) :
    ∃ g : Nat × Nat →. Nat, Partrec g ∧
      ∀ a n, (g (a, n)).Dom ↔
        markerDomain (familyEvent (fun i s => candidateLevel R a i s)) n := by
  classical
  obtain ⟨inst, hdec⟩ := candidateEvent_primrec R hR
  let _ := inst
  let test : (Nat × Nat) × Nat → Bool := fun p =>
    decide (familyEvent (fun i s => candidateLevel R p.1.1 i s) p.1.2 p.2)
  have htest : Primrec test := hdec
  refine ⟨markerSearch test, markerSearch_partrec test htest, ?_⟩
  intro a n
  rw [markerSearch_dom_iff]
  simp [test, markerDomain, markerHoles]
  by_cases h : familyEvent (fun i s => candidateLevel R a i s)
      (Nat.unpair n).1 (Nat.unpair n).2 <;> simp [h]

/-- Primitive-recursive existential-universal-existential normal forms
reduce to the cofinite numerical-domain predicate of closed lambda terms. -/
theorem closedCofinite_hard_primrec (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Primrec R) :
    ∃ f : Nat → Term, Primrec f ∧ ∀ a,
      ((∃ i, ∀ j, ∃ k, R (((a, i), j), k) = true) ↔
        ClosedCofiniteNumericalDomain (f a)) := by
  obtain ⟨g, hg, hdom⟩ := candidateMarker_partrec R hR
  change Nat.Partrec (fun n => Part.bind (Part.ofOption (Encodable.decode (α := Nat × Nat) n))
    fun p => (g p).map Encodable.encode) at hg
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hu' (a n : Nat) : Nat.Partrec.Code.eval u (Nat.pair a n) = g (a, n) := by
    have h := congrFun hu (Encodable.encode (a, n))
    simpa [Encodable.encode_prod_val, Part.map_id'] using h
  let f : Nat → Term := fun a => compileLambdaTotal (Nat.Partrec.Code.curry u a)
  have hf : Primrec f := primrec_compileLambdaTotal.comp
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id)
  refine ⟨f, hf, ?_⟩
  intro a
  have hs : Scoped 0 (f a) := (compileLambdaTotal_sound _).1
  have he (n : Nat) : numericalValue (f a) n = g (a, n) := by
    change numericalValue (compileLambdaTotal (Nat.Partrec.Code.curry u a)) n = g (a, n)
    rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry, hu']
  have hset : missingNumericalDomain (f a) =
      {n | ¬ markerDomain (familyEvent (fun i s => candidateLevel R a i s)) n} := by
    ext n
    simp [missingNumericalDomain, he, hdom]
  simp only [ClosedCofiniteNumericalDomain, hs, true_and, hset]
  exact (candidateMarker_cofinite_iff R a).symm

/-- The witness encodes both an original candidate witness and a finite
evaluation stage for a fixed code computing the original predicate. -/
def boundedCodePredicate (u : Nat.Partrec.Code)
    (p : ((Nat × Nat) × Nat) × Nat) : Bool :=
  decide (Nat.Partrec.Code.evaln (Nat.unpair p.2).2 u
    (Encodable.encode (p.1, (Nat.unpair p.2).1)) = some (Encodable.encode true))

theorem boundedCodePredicate_primrec (u : Nat.Partrec.Code) : Primrec (boundedCodePredicate u) := by
  let P := ((Nat × Nat) × Nat) × Nat
  have hun : Primrec (fun p : P => Nat.unpair p.2) := Primrec.unpair.comp Primrec.snd
  have hk : Primrec (fun p : P => (Nat.unpair p.2).1) := Primrec.fst.comp hun
  have hs : Primrec (fun p : P => (Nat.unpair p.2).2) := Primrec.snd.comp hun
  have harg : Primrec (fun p : P => (p.1, (Nat.unpair p.2).1)) := Primrec.fst.pair hk
  have heval : Primrec (fun p : P => Nat.Partrec.Code.evaln (Nat.unpair p.2).2 u
      (Encodable.encode (p.1, (Nat.unpair p.2).1))) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hs.pair (Primrec.const u)).pair (Primrec.encode.comp harg))
  exact (Primrec.eq.comp heval (Primrec.const _)).decide

/-- Every fixed computable Boolean test admits a primitive-recursive bounded
test after pairing its witness with an evaluation-stage witness. -/
theorem computablePredicate_bounded (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Computable R) :
    ∃ S : ((Nat × Nat) × Nat) × Nat → Bool, Primrec S ∧
      ∀ a i j, (∃ k, R (((a, i), j), k) = true) ↔
        ∃ w, S (((a, i), j), w) = true := by
  have hp : Partrec (fun p : ((Nat × Nat) × Nat) × Nat => Part.some (R p)) := hR.partrec
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := ((Nat × Nat) × Nat) × Nat) n)) fun p =>
      (Part.some (R p)).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hu' (p : ((Nat × Nat) × Nat) × Nat) :
      Nat.Partrec.Code.eval u (Encodable.encode p) = Part.some (Encodable.encode (R p)) := by
    have h := congrFun hu (Encodable.encode p)
    simpa only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_some] using h
  refine ⟨boundedCodePredicate u, boundedCodePredicate_primrec u, ?_⟩
  intro a i j
  constructor
  · rintro ⟨k, hk⟩
    have hv : Encodable.encode true ∈ Nat.Partrec.Code.eval u (Encodable.encode (((a, i), j), k)) := by
      rw [hu', hk]
      simp
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨Nat.pair k s, ?_⟩
    simpa [boundedCodePredicate, Nat.unpair_pair] using hs
  · rintro ⟨w, hw⟩
    let k := (Nat.unpair w).1
    let s := (Nat.unpair w).2
    have he : Nat.Partrec.Code.evaln s u (Encodable.encode (((a, i), j), k)) =
        some (Encodable.encode true) := by
      unfold boundedCodePredicate at hw
      exact of_decide_eq_true hw
    have hv : Encodable.encode true ∈ Nat.Partrec.Code.eval u (Encodable.encode (((a, i), j), k)) :=
      Nat.Partrec.Code.evaln_sound (by rw [he]; simp)
    rw [hu' (((a, i), j), k)] at hv
    have henc : Encodable.encode true = Encodable.encode (R (((a, i), j), k)) := by
      simpa using hv
    exact ⟨k, (Encodable.encode_injective henc).symm⟩

/-- Every computable existential-universal-existential Boolean normal form
reduces to cofinite numerical domains of closed lambda programs. -/
theorem closedCofinite_hard (R : ((Nat × Nat) × Nat) × Nat → Bool)
    (hR : Computable R) :
    ∃ f : Nat → Term, Primrec f ∧ ∀ a,
      ((∃ i, ∀ j, ∃ k, R (((a, i), j), k) = true) ↔
        ClosedCofiniteNumericalDomain (f a)) := by
  obtain ⟨S, hS, hconv⟩ := computablePredicate_bounded R hR
  obtain ⟨f, hf, hcorrect⟩ := closedCofinite_hard_primrec S hS
  refine ⟨f, hf, ?_⟩
  intro a
  rw [← hcorrect a]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, fun j => (hconv a i j).1 (hi j)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, fun j => (hconv a i j).2 (hi j)⟩

theorem closedCofinite_normalForm_complete :
    Primrec cofiniteBoundedWitness ∧
    (∃ f : Term → Nat.Partrec.Code, Primrec f ∧ ∀ t,
      (ClosedCofiniteNumericalDomain t ↔
        ∃ b, ∀ n, ∃ k, cofiniteBoundedWitness (((f t, b), n), k) = true)) ∧
    ∀ R : ((Nat × Nat) × Nat) × Nat → Bool, Computable R →
      ManyOneReducible (fun a => ∃ i, ∀ j, ∃ k, R (((a, i), j), k) = true)
        ClosedCofiniteNumericalDomain := by
  refine ⟨cofiniteBoundedWitness_primrec, closedCofinite_has_bounded_form, ?_⟩
  intro R hR
  obtain ⟨f, hf, hcorrect⟩ := closedCofinite_hard R hR
  exact ⟨f, hf.to_comp, hcorrect⟩

/-- Cofiniteness for standard recursive codes and for closed lambda terms is
equivalent under computable many-one reductions. -/
theorem codeCofinite_manyOne_closedCofinite :
    ManyOneReducible CodeCofinite ClosedCofiniteNumericalDomain := by
  refine ⟨compileLambdaTotal, primrec_compileLambdaTotal.to_comp, ?_⟩
  intro c
  have hs : Scoped 0 (compileLambdaTotal c) := (compileLambdaTotal_sound c).1
  simp only [ClosedCofiniteNumericalDomain, hs, true_and,
    finite_missing_iff_eventually_defined, (compileLambdaTotal_sound c).2]
  rfl

theorem closedCofinite_manyOne_codeCofinite :
    ManyOneReducible ClosedCofiniteNumericalDomain CodeCofinite := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  exact ⟨closedTotalityCode u, (closedTotalityCode_primrec u).to_comp,
    closedCofiniteCode_correct u hu⟩

theorem codeCofinite_manyOne_equiv :
    ManyOneEquiv CodeCofinite ClosedCofiniteNumericalDomain :=
  ⟨codeCofinite_manyOne_closedCofinite, closedCofinite_manyOne_codeCofinite⟩

#print axioms closedCofinite_has_bounded_form
#print axioms markerDomain_cofinite_iff
#print axioms monotone_unbounded_iff_late_increases
#print axioms familyMarker_cofinite_iff_unbounded
#print axioms candidateMarker_cofinite_iff
#print axioms candidateLevel_primrec
#print axioms candidateEvent_primrec
#print axioms closedCofinite_hard_primrec
#print axioms computablePredicate_bounded
#print axioms closedCofinite_normalForm_complete
#print axioms codeCofinite_manyOne_equiv
end LambdaTuring
