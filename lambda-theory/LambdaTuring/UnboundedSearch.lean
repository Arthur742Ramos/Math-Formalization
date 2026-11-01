/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ObservationSearch
public meta import LambdaTuring.ObservationSearch
public import Mathlib.Computability.Partrec

@[expose] public section

namespace LambdaTuring

/-- Search successively larger finite beta-reduction trees for a numeral. -/
noncomputable def searchResult (t : Term) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun fuel => (observations fuel t n).head?

theorem mem_searchResult_iff (t : Term) (n m : Nat) :
    m ∈ searchResult t n ↔ NumericalResult t n m := by
  constructor
  · intro h
    obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec h
    exact (numericalResult_iff_observed t n m).2 ⟨fuel, List.mem_of_mem_head? hfuel⟩
  · intro hm
    obtain ⟨fuel, hfuel⟩ := (numericalResult_iff_observed t n m).1 hm
    have hnonempty : observations fuel t n ≠ [] := List.ne_nil_of_mem hfuel
    have hdom : (searchResult t n).Dom := by
      apply Nat.rfindOpt_dom.2
      exact ⟨fuel, _, List.head_mem_head? hnonempty⟩
    obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 hdom
    have hresult : NumericalResult t n m' := by
      obtain ⟨i, hi⟩ := Nat.rfindOpt_spec hm'
      exact (numericalResult_iff_observed t n m').2 ⟨i, List.mem_of_mem_head? hi⟩
    have hEq : m' = m := numeral_result_unique hresult hm
    simpa [hEq] using hm'

theorem searchResult_eq_numericalValue (t : Term) (n : Nat) :
    searchResult t n = numericalValue t n := by
  apply Part.ext
  intro m
  rw [mem_searchResult_iff, mem_numericalValue_iff]


/-- If this particular bounded-tree observation test is computable, minimization
    yields partial-recursive numerical semantics. Its premise remains explicit;
    later modules instead prove the unconditional result via breadth-first search. -/
theorem numericalValue_partrec_of_boundedSearch (t : Term)
    (h : Computable₂ fun n fuel : Nat => (observations fuel t n).head?) :
    Nat.Partrec (numericalValue t) := by
  have hs : Partrec (fun n => searchResult t n) := Partrec.rfindOpt h
  have heq : (fun n => searchResult t n) = numericalValue t :=
    funext (searchResult_eq_numericalValue t)
  rw [heq] at hs
  exact Partrec.nat_iff.1 hs

#print axioms numericalValue_partrec_of_boundedSearch
#print axioms searchResult_eq_numericalValue

end LambdaTuring
