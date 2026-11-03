/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FragmentBridge
public meta import LambdaTuring.FragmentBridge
public import LambdaTuring.MachineBottom
public meta import LambdaTuring.MachineBottom

@[expose] public section

namespace LambdaTuring

/-- The two partial compilers agree on every source code both currently accept. -/
def compileCommonWithBottom (c : Nat.Partrec.Code) : Option (Term × (Σ states, Machine.Program states)) := do
  let t ← compileWithBottom c
  let p ← Machine.compileWithBottomMachine c
  pure (t, p)

theorem compileCommonWithBottom_factors (c : Nat.Partrec.Code) (t : Term)
    (p : Σ states, Machine.Program states) (h : compileCommonWithBottom c = some (t, p)) :
    compileWithBottom c = some t ∧ Machine.compileWithBottomMachine c = some p := by
  cases ht : compileWithBottom c with
  | none => simp [compileCommonWithBottom, ht] at h
  | some t' =>
    cases hp : Machine.compileWithBottomMachine c with
    | none => simp [compileCommonWithBottom, ht, hp] at h
    | some p' =>
      have heq : (t', p') = (t, p) := by simpa [compileCommonWithBottom, ht, hp] using h
      cases heq
      exact ⟨rfl, rfl⟩

theorem compileCommonWithBottom_numerical (c : Nat.Partrec.Code) (t : Term)
    (p : Σ states, Machine.Program states) (h : compileCommonWithBottom c = some (t, p)) (n m : Nat) :
    NumericalResult t n m ↔ Machine.MathYields p.2 n m := by
  obtain ⟨ht, hp⟩ := compileCommonWithBottom_factors c t p h
  rw [← mem_numericalValue_iff, (compileWithBottom_sound c t ht).2 n,
    ← Machine.compileWithBottomMachine_mathYields c p hp n m]

theorem compileCommonWithBottom_no_numerical (c : Nat.Partrec.Code) (t : Term)
    (p : Σ states, Machine.Program states) (h : compileCommonWithBottom c = some (t, p)) (n : Nat) :
    (∀ m, ¬ NumericalResult t n m) ↔ ∀ m, ¬ Machine.MathYields p.2 n m := by
  simp only [compileCommonWithBottom_numerical c t p h n]

theorem compileCommonWithBottom_bottom :
    compileCommonWithBottom bottomCode = some (cpsUnary cpsBottom, ⟨0, Machine.loopMachine⟩) := by
  simp [compileCommonWithBottom, compileWithBottom_bottom, Machine.compileWithBottomMachine_bottom]

theorem compileCommonWithBottom_other (c : Nat.Partrec.Code)
    (h : Encodable.encode c ≠ Encodable.encode bottomCode) :
    compileCommonWithBottom c = compileCommon c := by
  simp [compileCommonWithBottom, compileWithBottom, Machine.compileWithBottomMachine, h, compileCommon]

theorem zero_ne_bottom : Nat.Partrec.Code.zero ≠ bottomCode := by
  intro h
  cases h

theorem identity_ne_bottom : Nat.Partrec.Code.id ≠ bottomCode := by
  intro h
  cases h

theorem successor_ne_bottom : Nat.Partrec.Code.succ ≠ bottomCode := by
  intro h
  cases h

theorem compileCommonWithBottom_zero :
    compileCommonWithBottom Nat.Partrec.Code.zero = some (cpsUnary (cpsConstant 0), ⟨1, Machine.zeroMachine⟩) := by
  rw [compileCommonWithBottom_other _ (fun h => zero_ne_bottom (Encodable.encode_injective h))]
  exact compileCommon_zero

theorem compileCommonWithBottom_identity :
    compileCommonWithBottom Nat.Partrec.Code.id = some (cpsUnary cpsIdentity, ⟨0, Machine.immediateHalt⟩) := by
  rw [compileCommonWithBottom_other _ (fun h => identity_ne_bottom (Encodable.encode_injective h))]
  exact compileCommon_identity

theorem compileCommonWithBottom_successor :
    compileCommonWithBottom Nat.Partrec.Code.succ = some (cpsUnary cpsSuccessor, ⟨2, Machine.successorMachine⟩) := by
  rw [compileCommonWithBottom_other _ (fun h => successor_ne_bottom (Encodable.encode_injective h))]
  exact compileCommon_successor

theorem compileCommonWithBottom_domain (c : Nat.Partrec.Code) :
    (∃ t p, compileCommonWithBottom c = some (t, p)) ↔
      c = Nat.Partrec.Code.zero ∨ c = Nat.Partrec.Code.id ∨ c = Nat.Partrec.Code.succ ∨ c = bottomCode := by
  constructor
  · intro h
    by_cases hb : Encodable.encode c = Encodable.encode bottomCode
    · exact Or.inr (Or.inr (Or.inr (Encodable.encode_injective hb)))
    · have hc : ∃ t p, compileCommon c = some (t, p) := by
        simpa [compileCommonWithBottom_other c hb] using h
      rcases (compileCommon_domain c).1 hc with h0 | hi | hs
      · exact Or.inl h0
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hs))
  · rintro (h | h | h | h)
    · subst c; exact ⟨_, _, compileCommonWithBottom_zero⟩
    · subst c; exact ⟨_, _, compileCommonWithBottom_identity⟩
    · subst c; exact ⟨_, _, compileCommonWithBottom_successor⟩
    · subst c; exact ⟨_, _, compileCommonWithBottom_bottom⟩

/-- The shared fragment contains a genuinely undefined source code. -/
theorem bottom_common_no_result (n : Nat) :
    numericalValue (cpsUnary cpsBottom) n = Part.none ∧
      ∀ m, ¬ Machine.MathYields Machine.loopMachine n m := by
  constructor
  · simpa [bottomCode_eval] using (cpsUnary_represents cpsBottom_code).2 n
  · intro m hm
    exact Machine.loopMachine_no_yields n m ((Machine.math_yields_iff Machine.loopMachine n m).1 hm)

#print axioms compileCommonWithBottom_numerical
#print axioms compileCommonWithBottom_no_numerical
#print axioms bottom_common_no_result
#print axioms compileCommonWithBottom_domain

end LambdaTuring
