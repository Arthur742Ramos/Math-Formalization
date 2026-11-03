/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.DirectNormalObserver
public meta import LambdaTuring.DirectNormalObserver
public import LambdaTuring.MachineHaltBridge
public meta import LambdaTuring.MachineHaltBridge
@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- Any recursive code implementing the tagged normal observer compiles to a
finite machine with the same numerical observations. -/
theorem codeMachine_yields (c : Code)
    (hc : ∀ t, Code.eval c (directTermNumber t) = (normalObservation t).map Encodable.encode)
    (t : Term) (r : Option Nat) :
    Machine.Yields (compiledUnaryMachine c) (directTermNumber t) (Encodable.encode r) ↔
      r ∈ normalObservation t := by
  rw [compiledUnaryMachine_yields_iff, (compileLambdaTotal_sound c).2, hc t, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    have h : a = r := Encodable.encode_injective heq
    simpa [h] using ha
  · intro h
    exact ⟨r, h, rfl⟩

theorem codeMachine_numeral (c : Code)
    (hc : ∀ t, Code.eval c (directTermNumber t) = (normalObservation t).map Encodable.encode)
    (t : Term) (n : Nat) :
    Machine.Yields (compiledUnaryMachine c) (directTermNumber t) (n + 1) ↔
      Reaches t (church n) := by
  simpa [normalObservation_numeral_iff] using codeMachine_yields c hc t (some n)

theorem codeMachine_nonnumeral (c : Code)
    (hc : ∀ t, Code.eval c (directTermNumber t) = (normalObservation t).map Encodable.encode)
    (t : Term) :
    Machine.Yields (compiledUnaryMachine c) (directTermNumber t) 0 ↔
      (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧ ¬ ∃ n, Reaches t (church n) := by
  simpa [normalObservation_nonnumeral_iff] using codeMachine_yields c hc t Option.none

theorem codeMachine_no_halt (c : Code)
    (hc : ∀ t, Code.eval c (directTermNumber t) = (normalObservation t).map Encodable.encode)
    (t : Term) :
    (¬ ∃ d, Machine.Reaches (compiledUnaryMachine c) (Machine.initial (directTermNumber t)) d ∧
      Machine.Halted (compiledUnaryMachine c) d) ↔
      ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v := by
  rw [compiledUnaryMachine_halts_iff_yields]
  constructor
  · intro hnon hnormal
    have hdom : (normalObservation t).Dom := by
      by_contra hd
      have heq : normalObservation t = Part.none := Part.eq_none_iff.2 (by
        intro r hr
        exact hd (Part.dom_iff_mem.2 ⟨r, hr⟩))
      exact (normalObservation_undefined_iff t).1 heq hnormal
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.1 hdom
    exact hnon ⟨Encodable.encode r, (codeMachine_yields c hc t r).2 hr⟩
  · intro hnone ⟨m, hm⟩
    have h := (compiledUnaryMachine_yields_iff c (directTermNumber t) m).1 hm
    rw [(compileLambdaTotal_sound c).2, hc t,
      (normalObservation_undefined_iff t).2 hnone] at h
    simp at h

#print axioms codeMachine_yields
#print axioms codeMachine_numeral
#print axioms codeMachine_nonnumeral
#print axioms codeMachine_no_halt
end LambdaTuring
