/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchComputable
public meta import LambdaTuring.ChurchComputable
public import LambdaTuring.UnboundedSearch
public meta import LambdaTuring.UnboundedSearch
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LambdaTuring

/-- Breadth-first expansion retains previously reached terms. -/
def advance (ts : List Term) : List Term := ts ++ ts.flatMap betaSteps

def breadth : Nat → Term → List Term
  | 0, t => [t]
  | k + 1, t => advance (breadth k t)

theorem breadth_mono {k : Nat} {t u : Term} (h : u ∈ breadth k t) : u ∈ breadth (k + 1) t := by
  simp [breadth, advance, h]

theorem breadth_step {k : Nat} {t u v : Term}
    (h : u ∈ breadth k t) (hs : Beta u v) : v ∈ breadth (k + 1) t := by
  simp only [breadth, advance, List.mem_append, List.mem_flatMap, mem_betaSteps_iff]
  exact Or.inr ⟨u, h, hs⟩

theorem reaches_trans {a b c : Term} (hab : Reaches a b) (hbc : Reaches b c) : Reaches a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

theorem breadth_sound {k : Nat} {t u : Term} (h : u ∈ breadth k t) : Reaches t u := by
  induction k generalizing u with
  | zero =>
    simp [breadth] at h
    subst u
    exact .refl _
  | succ k ih =>
    simp only [breadth, advance, List.mem_append, List.mem_flatMap, mem_betaSteps_iff] at h
    rcases h with h | ⟨v, hv, hstep⟩
    · exact ih h
    · exact reaches_trans (ih hv) (.step hstep (.refl _))

theorem breadth_complete {t u : Term} (h : Reaches t u) : ∃ k, u ∈ breadth k t := by
  have rtc : Relation.ReflTransGen Beta t u := by
    induction h with
    | refl => exact .refl
    | step hs _ ih => exact .head hs ih
  clear h
  induction rtc with
  | refl => exact ⟨0, by simp [breadth]⟩
  | tail _ hs ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, breadth_step hk hs⟩

theorem reaches_iff_breadth (t u : Term) : Reaches t u ↔ ∃ k, u ∈ breadth k t :=
  ⟨breadth_complete, fun ⟨_, h⟩ => breadth_sound h⟩

def breadthObservations (k : Nat) (t : Term) (n : Nat) : List Nat :=
  (breadth k (.app t (church n))).filterMap decodeChurch

theorem numeral_iff_breadth (t : Term) (n m : Nat) :
    NumericalResult t n m ↔ ∃ k, m ∈ breadthObservations k t n := by
  simp [NumericalResult, breadthObservations, List.mem_filterMap, decodeChurch_iff, reaches_iff_breadth]

/-- Breadth-first enumeration is primitive recursive assuming the one-step enumerator is.
    Later modules prove that premise using effective capture-avoiding substitution. -/
theorem primrec_breadth_of_steps (hsteps : Primrec betaSteps) :
    Primrec₂ (fun t k => breadth k t) := by
  have hflat : Primrec (fun ts : List Term => ts.flatMap betaSteps) :=
    Primrec.list_flatMap Primrec.id (hsteps.comp Primrec.snd).to₂
  have hadv : Primrec advance := Primrec.list_append.comp Primrec.id hflat
  have hbase : Primrec (fun t : Term => [t]) :=
    Primrec.list_cons.comp Primrec.id (Primrec.const [])
  have hstep : Primrec₂ (fun (_ : Term) (p : Nat × List Term) => advance p.2) :=
    hadv.comp (Primrec.snd.comp Primrec.snd)
  have hrec := Primrec.nat_rec hbase hstep
  exact hrec.of_eq (fun t k => by induction k <;> simp [breadth, *])

theorem computable_breadthObservations_of_steps (hsteps : Primrec betaSteps) (t : Term) :
    Computable₂ (fun n k => (breadthObservations k t n).head?) := by
  have hstart : Primrec (fun p : Nat × Nat => Term.app t (church p.1)) :=
    primrec_app.comp (Primrec.const t) (primrec_church.comp Primrec.fst)
  have hlist : Primrec (fun p : Nat × Nat => breadth p.2 (Term.app t (church p.1))) :=
    (primrec_breadth_of_steps hsteps).comp hstart Primrec.snd
  have hfilter : Primrec (fun p : Nat × Nat => (breadth p.2 (Term.app t (church p.1))).filterMap decodeChurch) :=
    Primrec.listFilterMap hlist (primrec_decodeChurch.comp Primrec.snd).to₂
  exact (Primrec.list_head?.comp hfilter).to_comp

noncomputable def breadthSearch (t : Term) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun k => (breadthObservations k t n).head?

theorem mem_breadthSearch_iff (t : Term) (n m : Nat) :
    m ∈ breadthSearch t n ↔ NumericalResult t n m := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec h
    exact (numeral_iff_breadth t n m).2 ⟨k, List.mem_of_mem_head? hk⟩
  · intro hm
    obtain ⟨k, hk⟩ := (numeral_iff_breadth t n m).1 hm
    have hn : breadthObservations k t n ≠ [] := List.ne_nil_of_mem hk
    have hd : (breadthSearch t n).Dom := by
      apply Nat.rfindOpt_dom.2
      exact ⟨k, _, List.head_mem_head? hn⟩
    obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 hd
    have hr : NumericalResult t n m' := by
      obtain ⟨j, hj⟩ := Nat.rfindOpt_spec hm'
      exact (numeral_iff_breadth t n m').2 ⟨j, List.mem_of_mem_head? hj⟩
    have heq : m' = m := numeral_result_unique hr hm
    simpa [heq] using hm'

theorem breadthSearch_eq_numericalValue (t : Term) (n : Nat) :
    breadthSearch t n = numericalValue t n := by
  apply Part.ext
  intro m
  rw [mem_breadthSearch_iff, mem_numericalValue_iff]

/-- One-step enumeration suffices for lambda observations to be partial recursive.
    `SubstTable` later proves the premise and derives the unconditional result. -/
theorem numericalValue_partrec_of_steps (hsteps : Primrec betaSteps) (t : Term) :
    Nat.Partrec (numericalValue t) := by
  have hs : Partrec (fun n => breadthSearch t n) :=
    Partrec.rfindOpt (computable_breadthObservations_of_steps hsteps t)
  have heq : (fun n => breadthSearch t n) = numericalValue t :=
    funext (breadthSearch_eq_numericalValue t)
  rw [heq] at hs
  exact Partrec.nat_iff.1 hs

#print axioms numericalValue_partrec_of_steps

end LambdaTuring
