/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchComputable
public meta import LambdaTuring.ChurchComputable
public import LambdaTuring.NumericalSemantics
public meta import LambdaTuring.NumericalSemantics
public import LambdaTuring.Observation
public meta import LambdaTuring.Observation

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- A closed lambda term returning the Church numeral `n` for every input. -/
def constantTerm (n : Nat) : Term := .abs (church n)

theorem subst_churchBody_above (n depth : Nat) (value : Term) :
    substAt (depth + 2) value (churchBody n) = churchBody n := by
  induction n with
  | zero => simp [churchBody, substAt]
  | succ n ih => simp [churchBody, substAt, ih]

theorem subst_church (n : Nat) (value : Term) : substAt 0 value (church n) = church n := by
  simpa [church, substAt] using congrArg (fun t => Term.abs (Term.abs t))
    (subst_churchBody_above n 0 value)

theorem constantTerm_closed (n : Nat) : Scoped 0 (constantTerm n) := by
  have h : Scoped 3 (churchBody n) := by
    induction n with
    | zero => simp [churchBody, Scoped]
    | succ n ih => simpa [churchBody, Scoped] using ih
  exact h

theorem constantTerm_reaches (n input : Nat) :
    Reaches (.app (constantTerm n) (church input)) (church n) := by
  apply Reaches.step (Beta.contract _ _)
  rw [subst_church]
  exact Reaches.refl _

theorem constantTerm_represents (n : Nat) : Represents (constantTerm n) (Code.eval (Code.const n)) := by
  constructor
  · exact constantTerm_closed n
  · intro input
    rw [Code.eval_const, numericalValue_some_iff]
    exact constantTerm_reaches n input

/-- A partial compiler with an explicit, decidable constant-code domain.
    Failure means the code is outside this fragment, not that it diverges. -/
def compileConstant (c : Code) : Option Term := (decodeConst c).map constantTerm

theorem compileConstant_const (n : Nat) :
    compileConstant (Code.const n) = some (constantTerm n) := by
  simp [compileConstant, decodeConst_const]

theorem compileConstant_sound (c : Code) (t : Term) (h : compileConstant c = some t) :
    Represents t (Code.eval c) := by
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  have hc := decodeConst_sound c n hn
  subst c
  exact constantTerm_represents n

theorem primrec_constantTerm : Primrec constantTerm :=
  primrec_abs.comp primrec_church

theorem primrec_compileConstant : Primrec compileConstant :=
  (Primrec.option_map₁ primrec_constantTerm).comp primrec_decodeConst

theorem identityTerm_represents : Represents identityTerm (Code.eval Code.id) := by
  constructor
  · simp [Scoped, identityTerm]
  · intro input
    rw [Code.eval_id, numericalValue_some_iff]
    exact Reaches.step (Beta.contract _ _) (Reaches.refl _)

/-- Extend the explicit constant-code compiler with Mathlib's identity code. -/
def compileBase (c : Code) : Option Term :=
  if Encodable.encode c = Encodable.encode Code.id then some identityTerm else compileConstant c

theorem compileBase_id : compileBase Code.id = some identityTerm := by
  simp [compileBase]

theorem compileBase_const (n : Nat) : compileBase (Code.const n) = some (constantTerm n) := by
  have hne : Code.const n ≠ Code.id := by cases n <;> simp [Code.const, Code.id]
  have h : Encodable.encode (Code.const n) ≠ Encodable.encode Code.id :=
    fun eq => hne (Encodable.encode_injective eq)
  simp [compileBase, h, compileConstant_const]

theorem compileBase_sound (c : Code) (t : Term) (h : compileBase c = some t) :
    Represents t (Code.eval c) := by
  by_cases hc : Encodable.encode c = Encodable.encode Code.id
  · have heq : c = Code.id := Encodable.encode_injective hc
    subst c
    have ht : identityTerm = t := by simpa [compileBase] using h
    subst t
    exact identityTerm_represents
  · exact compileConstant_sound c t (by simpa [compileBase, hc] using h)

theorem primrec_compileBase : Primrec compileBase :=
  Primrec.ite (Primrec.eq.comp Primrec.encode (Primrec.const (Encodable.encode Code.id)))
    (Primrec.const (some identityTerm)) primrec_compileConstant

#print axioms compileConstant_sound
#print axioms primrec_compileConstant
#print axioms compileBase_sound
#print axioms primrec_compileBase

end LambdaTuring
