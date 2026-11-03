/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.NormalOrder
public meta import LambdaTuring.NormalOrder
@[expose] public section

namespace LambdaTuring

theorem normalOrderRun_fixed {t : Term} (h : normalOrderStep t = none) (k : Nat) :
    normalOrderRun k t = t := by
  induction k with
  | zero => rfl
  | succ k ih => simp [normalOrderRun, h]

theorem normalOrderRun_succ_end (k : Nat) (t : Term) :
    normalOrderRun (k + 1) t =
      (normalOrderStep (normalOrderRun k t)).getD (normalOrderRun k t) := by
  induction k generalizing t with
  | zero => cases h : normalOrderStep t <;> simp [normalOrderRun, h]
  | succ k ih =>
    cases h : normalOrderStep t with
    | none => simp [normalOrderRun, h]
    | some u => simpa [normalOrderRun, h] using ih u

theorem primrec_normalOrderRun : Primrec₂ (fun t k => normalOrderRun k t) := by
  have hnext : Primrec (fun t => (normalOrderStep t).getD t) :=
    Primrec.option_getD.comp normalOrderStep_primrec Primrec.id
  have hstep : Primrec₂ (fun (_ : Term) (p : Nat × Term) =>
      (normalOrderStep p.2).getD p.2) :=
    hnext.comp (Primrec.snd.comp Primrec.snd)
  have hrec := Primrec.nat_rec Primrec.id hstep
  apply hrec.of_eq
  intro t k
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.rec t (fun _ z => (normalOrderStep z).getD z) k = normalOrderRun k t at ih
    simp only [normalOrderRun_succ_end]
    change (normalOrderStep (Nat.rec t (fun _ z => (normalOrderStep z).getD z) k)).getD
      (Nat.rec t (fun _ z => (normalOrderStep z).getD z) k) = _
    rw [ih]

/-- Outer none means continue; some none is a nonnumerical normal form. -/
def normalObservationStage (t : Term) (k : Nat) : Option (Option Nat) :=
  match normalOrderStep (normalOrderRun k t) with
  | none => some (decodeChurch (normalOrderRun k t))
  | some _ => none

theorem normalObservationStage_primrec : Primrec₂ normalObservationStage := by
  let run : Term × Nat → Term := fun p => normalOrderRun p.2 p.1
  have hr : Primrec run := primrec_normalOrderRun.comp Primrec.fst Primrec.snd
  have hs : Primrec (fun p : Term × Nat => normalOrderStep (run p)) :=
    normalOrderStep_primrec.comp hr
  have hn : Primrec (fun p : Term × Nat => some (decodeChurch (run p))) :=
    Primrec.option_some.comp (primrec_decodeChurch.comp hr)
  have hy : Primrec₂ (fun (_ : Term × Nat) (_ : Term) => (none : Option (Option Nat))) :=
    Primrec.const none
  have h : Primrec (fun p : Term × Nat => normalObservationStage p.1 p.2) := by
    apply (Primrec.option_casesOn hs hn hy).of_eq
    intro p
    cases he : normalOrderStep (run p) <;> simp [normalObservationStage, run, he]
  exact h.to₂

noncomputable def normalObservation (t : Term) : Part (Option Nat) :=
  Nat.rfindOpt (normalObservationStage t)

theorem normalObservation_partrec : Partrec normalObservation :=
  Partrec.rfindOpt normalObservationStage_primrec.to_comp

theorem normal_forms_unique {t u v : Term} (hu : Reaches t u) (hv : Reaches t v)
    (hnu : ¬ ∃ x, Beta u x) (hnv : ¬ ∃ x, Beta v x) : u = v := by
  obtain ⟨w, huw, hvw⟩ := beta_confluent hu hv
  exact (normal_reaches_eq hnu huw).trans (normal_reaches_eq hnv hvw).symm

theorem mem_normalObservation_iff (t : Term) (r : Option Nat) :
    r ∈ normalObservation t ↔
      ∃ u, Reaches t u ∧ (¬ ∃ v, Beta u v) ∧ decodeChurch u = r := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec h
    cases hs : normalOrderStep (normalOrderRun k t) with
    | none =>
      refine ⟨_, normalOrderRun_reaches k t, (normalOrderStep_none_iff _).1 hs, ?_⟩
      simpa [normalObservationStage, hs] using hk
    | some u => simp [normalObservationStage, hs] at hk
  · rintro ⟨u, hu, hn, hd⟩
    obtain ⟨k, hrun, hstop⟩ := normalOrder_normalizes_to hu hn
    have hsu : normalOrderStep u = none := (normalOrderStep_none_iff _).2 hn
    have hdom : (normalObservation t).Dom := by
      apply Nat.rfindOpt_dom.2
      exact ⟨k, r, by simp [normalObservationStage, hrun, hsu, hd]⟩
    obtain ⟨r', hr'⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨j, hj⟩ := Nat.rfindOpt_spec hr'
    cases hs : normalOrderStep (normalOrderRun j t) with
    | none =>
      have heq : normalOrderRun j t = u := normal_forms_unique
        (normalOrderRun_reaches j t) hu ((normalOrderStep_none_iff _).1 hs) hn
      have hr : r' = r := by simpa [normalObservationStage, heq, hsu, hd] using hj.symm
      simpa [hr] using hr'
    | some v => simp [normalObservationStage, hs] at hj

/-- A numerical answer is exactly full-beta reachability of that numeral. -/
theorem normalObservation_numeral_iff (t : Term) (n : Nat) :
    some n ∈ normalObservation t ↔ Reaches t (church n) := by
  rw [mem_normalObservation_iff]
  constructor
  · rintro ⟨u, hu, _, hd⟩
    have heq := (decodeChurch_iff u n).1 hd
    simpa [heq] using hu
  · intro hu
    exact ⟨church n, hu, church_no_beta n, (decodeChurch_iff _ _).2 rfl⟩

/-- A defined `none` denotes a reachable nonnumerical normal form. -/
theorem normalObservation_nonnumeral_iff (t : Term) :
    none ∈ normalObservation t ↔
      (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧
        ¬ ∃ n, Reaches t (church n) := by
  rw [mem_normalObservation_iff]
  constructor
  · rintro ⟨u, hu, hn, hd⟩
    refine ⟨⟨u, hu, hn⟩, ?_⟩
    rintro ⟨n, hnum⟩
    have heq := normal_forms_unique hu hnum hn (church_no_beta n)
    have hsome := (decodeChurch_iff u n).2 heq
    rw [hd] at hsome
    cases hsome
  · rintro ⟨⟨u, hu, hn⟩, hnone⟩
    refine ⟨u, hu, hn, ?_⟩
    cases hd : decodeChurch u with
    | none => rfl
    | some n =>
      exfalso
      exact hnone ⟨n, by simpa [(decodeChurch_iff u n).1 hd] using hu⟩

/-- Search diverges exactly when there is no reachable beta-normal form. -/
theorem normalObservation_undefined_iff (t : Term) :
    normalObservation t = Part.none ↔
      ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v := by
  rw [Part.eq_none_iff]
  constructor
  · intro h ⟨u, hu, hn⟩
    exact h (decodeChurch u) ((mem_normalObservation_iff t _).2 ⟨u, hu, hn, rfl⟩)
  · intro h r hr
    obtain ⟨u, hu, hn, _⟩ := (mem_normalObservation_iff t r).1 hr
    exact h ⟨u, hu, hn⟩

/-- The eta-expanded zero from the CPS probe is not a numeral, despite its
positive operational zero-test result. -/
def etaObservationZero : Term := .abs (.abs (.abs (.app (.var 1) (.var 0))))

theorem etaObservationZero_normal : ¬ ∃ u, Beta etaObservationZero u := by
  rintro ⟨_, h⟩
  cases h with
  | abs h =>
    cases h with
    | abs h =>
      cases h with
      | abs h =>
        cases h with
        | appLeft h => cases h
        | appRight h => cases h

theorem etaObservationZero_ne_numeral (n : Nat) : etaObservationZero ≠ church n := by
  cases n <;> simp [etaObservationZero, church, churchBody]

theorem etaObservationZero_observer : none ∈ normalObservation etaObservationZero := by
  apply (normalObservation_nonnumeral_iff _).2
  refine ⟨⟨_, .refl _, etaObservationZero_normal⟩, ?_⟩
  rintro ⟨n, h⟩
  exact etaObservationZero_ne_numeral n (normal_reaches_eq etaObservationZero_normal h)

theorem omega_normalObservation_undefined : normalObservation omegaTerm = Part.none := by
  exact (normalObservation_undefined_iff _).2 omega_no_normal

#print axioms primrec_normalOrderRun
#print axioms normalObservation_partrec
#print axioms mem_normalObservation_iff
#print axioms normalObservation_numeral_iff
#print axioms normalObservation_nonnumeral_iff
#print axioms normalObservation_undefined_iff
#print axioms etaObservationZero_observer
#print axioms omega_normalObservation_undefined

end LambdaTuring
