/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineCoding
public meta import LambdaTuring.MachineCoding
public import LambdaTuring.MachineSearch
public meta import LambdaTuring.MachineSearch

@[expose] public section

namespace LambdaTuring.Machine

/-- Run exactly the specified number of transitions, failing on an earlier halt. -/
def runExact {states : Nat} (p : Program states) : Nat → Config states → Option (Config states)
  | 0, c => some c
  | fuel + 1, c => (runExact p fuel c).bind (step p)

theorem runExact_succ_start {states : Nat} (p : Program states) (fuel : Nat) (c : Config states) :
    runExact p (fuel + 1) c = (step p c).bind (runExact p fuel) := by
  induction fuel generalizing c with
  | zero => cases h : step p c <;> simp [runExact, h]
  | succ fuel ih =>
    change (runExact p (fuel + 1) c).bind (step p) =
      (step p c).bind (runExact p (fuel + 1))
    rw [ih c, Option.bind_assoc]
    rfl

theorem runExact_sound {states : Nat} (p : Program states) (fuel : Nat) (start target : Config states)
    (h : runExact p fuel start = some target) : Reaches p start target := by
  induction fuel generalizing start with
  | zero =>
    simp [runExact] at h
    subst target
    exact .refl _
  | succ fuel ih =>
    rw [runExact_succ_start] at h
    cases hs : step p start with
    | none => simp [hs] at h
    | some next =>
      have hn : runExact p fuel next = some target := by simpa [hs] using h
      exact .step hs (ih next hn)

theorem runExact_complete {states : Nat} {p : Program states} {start target : Config states}
    (h : Reaches p start target) : ∃ fuel, runExact p fuel start = some target := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih
    exact ⟨fuel + 1, by rw [runExact_succ_start]; simp [hs, hf]⟩

def observeExact {states : Nat} (p : Program states) (n fuel : Nat) : Option Nat :=
  (runExact p fuel (initial n)).bind fun c =>
    if step p c = none then decode (c.tape.head :: c.tape.right) else none

theorem yields_iff_observeExact {states : Nat} (p : Program states) (n m : Nat) :
    Yields p n m ↔ ∃ fuel, observeExact p n fuel = some m := by
  constructor
  · rintro ⟨c, hr, hh, hd⟩
    obtain ⟨fuel, hf⟩ := runExact_complete hr
    exact ⟨fuel, by simp [observeExact, hf, Halted] at hh ⊢; simp [hh, hd]⟩
  · rintro ⟨fuel, hf⟩
    cases hc : runExact p fuel (initial n) with
    | none => simp [observeExact, hc] at hf
    | some c =>
      by_cases hh : step p c = none
      · have hd : decode (c.tape.head :: c.tape.right) = some m := by
          simpa [observeExact, hc, hh] using hf
        exact ⟨c, runExact_sound p fuel _ c hc, hh, hd⟩
      · simp [observeExact, hc, hh] at hf

theorem primrec_runExact {states : Nat} (p : Program states) :
    Primrec₂ (fun c fuel => runExact p fuel c) := by
  have hb : Primrec (fun c : Config states => some c) := Primrec.option_some
  have hs : Primrec₂ (fun (_ : Config states) (q : Nat × Option (Config states)) =>
      q.2.bind (step p)) :=
    Primrec.option_bind (Primrec.snd.comp Primrec.snd)
      ((primrec_step p).comp Primrec.snd).to₂
  have h := Primrec.nat_rec hb hs
  apply h.of_eq
  intro c fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [runExact, ih]

theorem primrec_observeExact {states : Nat} (p : Program states) : Primrec₂ (observeExact p) := by
  let I := Nat × Nat
  let Q := I × Config states
  have hstart : Primrec (fun i : I => initial (states := states) i.1) :=
    (primrec_initial states).comp Primrec.fst
  have hrun : Primrec (fun i : I => runExact p i.2 (initial i.1)) :=
    (primrec_runExact p).comp hstart Primrec.snd
  have hc : Primrec (fun q : Q => q.2) := Primrec.snd
  have ht : Primrec (fun q : Q => q.2.tape) :=
    (Primrec.snd.comp (primrec_configParts states)).comp hc
  have hd : Primrec (fun q : Q => decode (q.2.tape.head :: q.2.tape.right)) :=
    primrec_decode.comp (Primrec.list_cons.comp (primrec_tapeHead.comp ht) (primrec_tapeRight.comp ht))
  have hp : Primrec₂ (fun (_ : I) (c : Config states) =>
      if step p c = none then decode (c.tape.head :: c.tape.right) else none) :=
    Primrec.ite (Primrec.eq.comp ((primrec_step p).comp hc) (Primrec.const none)) hd (Primrec.const none)
  exact Primrec.option_bind hrun hp

noncomputable def exactValue {states : Nat} (p : Program states) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun fuel => observeExact p n fuel

theorem mem_exactValue_iff {states : Nat} (p : Program states) (n m : Nat) :
    m ∈ exactValue p n ↔ Yields p n m := by
  constructor
  · intro hm
    obtain ⟨fuel, hf⟩ := Nat.rfindOpt_spec hm
    exact (yields_iff_observeExact p n m).2 ⟨fuel, by simpa using hf⟩
  · intro hm
    obtain ⟨fuel, hf⟩ := (yields_iff_observeExact p n m).1 hm
    have hd : (exactValue p n).Dom := Nat.rfindOpt_dom.2 ⟨fuel, m, by simpa using hf⟩
    obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 hd
    obtain ⟨fuel', hf'⟩ := Nat.rfindOpt_spec hm'
    have hy : Yields p n m' := (yields_iff_observeExact p n m').2 ⟨fuel', by simpa using hf'⟩
    have heq : m' = m := yields_unique hy hm
    simpa [heq] using hm'

theorem exactValue_eq_machineValue {states : Nat} (p : Program states) :
    exactValue p = machineValue p := by
  funext n
  apply Part.ext
  intro m
  rw [mem_exactValue_iff, mem_machineValue_iff]

/-- Every finite table machine has partial recursive numerical observations. -/
theorem machineValue_partrec {states : Nat} (p : Program states) : Nat.Partrec (machineValue p) := by
  have h : Partrec (exactValue p) := Partrec.rfindOpt (primrec_observeExact p).to_comp
  rw [exactValue_eq_machineValue] at h
  exact Partrec.nat_iff.1 h

#print axioms yields_iff_observeExact
#print axioms primrec_runExact
#print axioms machineValue_partrec

end LambdaTuring.Machine
