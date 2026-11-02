/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.SemanticBridge
public meta import LambdaTuring.SemanticBridge
public import Mathlib.Data.PFun

@[expose] public section

/-! Numerical observation under full beta reduction as a partial function. -/

namespace LambdaTuring

/-- A numerical result is a reachable Church numeral, regardless of the path taken. -/
def NumericalResult (t : Term) (n m : Nat) : Prop :=
  Reaches (.app t (church n)) (church m)

/-- The unique numerical observation, or an undefined partial value if no numeral is reachable. -/
noncomputable def numericalValue (t : Term) (n : Nat) : Part Nat :=
  ⟨∃ m, NumericalResult t n m, fun h => Classical.choose h⟩

theorem mem_numericalValue_iff (t : Term) (n m : Nat) :
    m ∈ numericalValue t n ↔ NumericalResult t n m := by
  rw [numericalValue, Part.mem_mk_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact Classical.choose_spec h
  · intro hm
    let h : ∃ m, NumericalResult t n m := ⟨m, hm⟩
    exact ⟨h, numeral_result_unique (Classical.choose_spec h) hm⟩

theorem numericalValue_some_iff (t : Term) (n m : Nat) :
    numericalValue t n = Part.some m ↔ NumericalResult t n m := by
  rw [Part.eq_some_iff, mem_numericalValue_iff]

theorem numericalValue_none_iff (t : Term) (n : Nat) :
    numericalValue t n = Part.none ↔ ∀ m, ¬ NumericalResult t n m := by
  simp only [Part.eq_none_iff, mem_numericalValue_iff]

/-- A closed term computes the partial function exactly on numerical observations. -/
def Represents (t : Term) (f : Nat →. Nat) : Prop :=
  Scoped 0 t ∧ ∀ n, numericalValue t n = f n

def LambdaComputable (f : Nat →. Nat) : Prop := ∃ t, Represents t f

#print axioms mem_numericalValue_iff
#print axioms numericalValue_none_iff

end LambdaTuring
