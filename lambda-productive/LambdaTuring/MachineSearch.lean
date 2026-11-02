/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineRun
public meta import LambdaTuring.MachineRun
public import Mathlib.Computability.Partrec

@[expose] public section

namespace LambdaTuring.Machine

/-- Search every finite execution bound for an accepted numerical halt. -/
noncomputable def machineValue {states : Nat} (p : Program states) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun fuel => observeWithin p n fuel

theorem mem_machineValue_iff {states : Nat} (p : Program states) (n m : Nat) :
    m ∈ machineValue p n ↔ Yields p n m := by
  constructor
  · intro hm
    obtain ⟨fuel, hf⟩ := Nat.rfindOpt_spec hm
    apply (yields_iff_observeWithin p n m).2
    exact ⟨fuel, by simpa using hf⟩
  · intro hm
    obtain ⟨fuel, hf⟩ := (yields_iff_observeWithin p n m).1 hm
    have hd : (machineValue p n).Dom := by
      apply Nat.rfindOpt_dom.2
      exact ⟨fuel, m, by simpa using hf⟩
    obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 hd
    obtain ⟨fuel', hf'⟩ := Nat.rfindOpt_spec hm'
    have hy : Yields p n m' := (yields_iff_observeWithin p n m').2
      ⟨fuel', by simpa using hf'⟩
    have heq : m' = m := yields_unique hy hm
    simpa [heq] using hm'

theorem machineValue_none_iff {states : Nat} (p : Program states) (n : Nat) :
    machineValue p n = Part.none ↔ ∀ m, ¬ Yields p n m := by
  simp only [Part.eq_none_iff, mem_machineValue_iff]

/-- The only remaining premise is effectiveness of bounded observation. -/
theorem machineValue_partrec_of_bounded {states : Nat} (p : Program states)
    (h : Computable₂ (fun n fuel => observeWithin p n fuel)) : Nat.Partrec (machineValue p) :=
  Partrec.nat_iff.1 (Partrec.rfindOpt h)

#print axioms mem_machineValue_iff
#print axioms machineValue_partrec_of_bounded

end LambdaTuring.Machine
