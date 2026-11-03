/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSWithSuccessor
public meta import LambdaTuring.CPSWithSuccessor
public import LambdaTuring.MachineSuccessor
public meta import LambdaTuring.MachineSuccessor

@[expose] public section

namespace LambdaTuring

/-- Compile a source code only when both current fragment compilers accept it. -/
def compileCommon (c : Nat.Partrec.Code) : Option (Term × (Σ states, Machine.Program states)) := do
  let t ← compileSuccessorFragment c
  let p ← Machine.compileSuccessorMachine c
  pure (t, p)

theorem compileCommon_factors (c : Nat.Partrec.Code) (t : Term) (p : Σ states, Machine.Program states)
    (h : compileCommon c = some (t, p)) :
    compileSuccessorFragment c = some t ∧ Machine.compileSuccessorMachine c = some p := by
  cases ht : compileSuccessorFragment c with
  | none => simp [compileCommon, ht] at h
  | some t' =>
    cases hp : Machine.compileSuccessorMachine c with
    | none => simp [compileCommon, ht, hp] at h
    | some p' =>
      have heq : (t', p') = (t, p) := by simpa [compileCommon, ht, hp] using h
      cases heq
      exact ⟨rfl, rfl⟩

theorem compileCommon_numerical (c : Nat.Partrec.Code) (t : Term) (p : Σ states, Machine.Program states)
    (h : compileCommon c = some (t, p)) (n m : Nat) :
    NumericalResult t n m ↔ Machine.MathYields p.2 n m := by
  obtain ⟨ht, hp⟩ := compileCommon_factors c t p h
  rw [← mem_numericalValue_iff, (compileSuccessorFragment_sound c t ht).2 n,
    ← Machine.compileSuccessorMachine_mathYields c p hp n m]

theorem compileCommon_no_numerical (c : Nat.Partrec.Code) (t : Term) (p : Σ states, Machine.Program states)
    (h : compileCommon c = some (t, p)) (n : Nat) :
    (∀ m, ¬ NumericalResult t n m) ↔ ∀ m, ¬ Machine.MathYields p.2 n m := by
  simp only [compileCommon_numerical c t p h n]

theorem compileCommon_zero :
    compileCommon Nat.Partrec.Code.zero = some (cpsUnary (cpsConstant 0), ⟨1, Machine.zeroMachine⟩) := by
  have h : compileCPSSuccessor Nat.Partrec.Code.zero = some (cpsConstant 0) := by
    simpa [Nat.Partrec.Code.const] using compileCPSSuccessor_const 0
  simp [compileCommon, compileSuccessorFragment, h, Machine.compileSuccessorMachine_zero]

theorem compileCommon_identity :
    compileCommon Nat.Partrec.Code.id = some (cpsUnary cpsIdentity, ⟨0, Machine.immediateHalt⟩) := by
  simp [compileCommon, compileSuccessorFragment, compileCPSSuccessor_id, Machine.compileSuccessorMachine_id]

theorem compileCommon_successor :
    compileCommon Nat.Partrec.Code.succ = some (cpsUnary cpsSuccessor, ⟨2, Machine.successorMachine⟩) := by
  simp [compileCommon, compileSuccessorFragment, compileCPSSuccessor_succ, Machine.compileSuccessorMachine_succ]

/-- The common compiler's current domain is exactly the three named codes. -/
theorem compileCommon_domain (c : Nat.Partrec.Code) :
    (∃ t p, compileCommon c = some (t, p)) ↔
      c = Nat.Partrec.Code.zero ∨ c = Nat.Partrec.Code.id ∨ c = Nat.Partrec.Code.succ := by
  constructor
  · rintro ⟨t, p, h⟩
    obtain ⟨_, hp⟩ := compileCommon_factors c t p h
    by_cases hs : Encodable.encode c = Encodable.encode Nat.Partrec.Code.succ
    · exact Or.inr (Or.inr (Encodable.encode_injective hs))
    · have hb : Machine.compileBasicMachine c = some p := by
        simpa only [Machine.compileSuccessorMachine, ite_eq_right hs] using hp
      by_cases hi : Encodable.encode c = Encodable.encode Nat.Partrec.Code.id
      · exact Or.inr (Or.inl (Encodable.encode_injective hi))
      · by_cases hz : Encodable.encode c = Encodable.encode Nat.Partrec.Code.zero
        · exact Or.inl (Encodable.encode_injective hz)
        · have impossible : (none : Option (Σ states, Machine.Program states)) = some p := by
            simpa only [Machine.compileBasicMachine, ite_eq_right hi, ite_eq_right hz] using hb
          cases impossible
  · rintro (h | h | h)
    · subst c; exact ⟨_, _, compileCommon_zero⟩
    · subst c; exact ⟨_, _, compileCommon_identity⟩
    · subst c; exact ⟨_, _, compileCommon_successor⟩

#print axioms compileCommon_numerical
#print axioms compileCommon_no_numerical
#print axioms compileCommon_domain

end LambdaTuring
