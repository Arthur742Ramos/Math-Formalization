/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputEndToEnd
public meta import LambdaTuring.OutputEndToEnd
public import LambdaTuring.ExtensionalCompleteness
public meta import LambdaTuring.ExtensionalCompleteness

@[expose] public section

namespace LambdaTuring

/- This uses Mathlib's existential code theorem. It establishes the full
extensional class equivalence but does not supply an effective extractor
from arbitrary lambda or machine syntax. -/
theorem partrec_iff_unaryMachine (f : Nat →. Nat) :
    Nat.Partrec f ↔ ∃ (states : Nat) (p : Machine.Program states),
      ∀ n m, Machine.Yields p n m ↔ m ∈ f n := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
    refine ⟨_, compiledUnaryMachine c, ?_⟩
    intro n m
    rw [compiledUnaryMachine_yields_iff, (compileLambdaTotal_sound c).2 n, hc]
  · rintro ⟨states, p, hp⟩
    have heq : Machine.machineValue p = f := by
      funext n
      apply Part.ext
      intro m
      rw [Machine.mem_machineValue_iff, hp n m]
    rw [← heq]
    exact Machine.machineValue_partrec p

theorem lambdaComputable_iff_unaryMachine (f : Nat →. Nat) :
    LambdaComputable f ↔ ∃ (states : Nat) (p : Machine.Program states),
      ∀ n m, Machine.Yields p n m ↔ m ∈ f n :=
  (lambdaComputable_iff_partrec f).trans (partrec_iff_unaryMachine f)

theorem lambda_unaryMachine_exists (t : Term) :
    ∃ (states : Nat) (p : Machine.Program states), ∀ n m,
      NumericalResult t n m ↔ Machine.Yields p n m := by
  obtain ⟨states, p, hp⟩ := (partrec_iff_unaryMachine (numericalValue t)).1
    (numericalValue_partrec t)
  refine ⟨states, p, ?_⟩
  intro n m
  rw [hp n m, mem_numericalValue_iff]

theorem unaryMachine_lambda_exists {states : Nat} (p : Machine.Program states) :
    ∃ t, Scoped 0 t ∧ ∀ n m, NumericalResult t n m ↔ Machine.Yields p n m := by
  obtain ⟨t, ht, h⟩ := machine_lambda_exists p
  exact ⟨t, ht, fun n m => (h n m).trans (Machine.math_yields_iff p n m)⟩

theorem lambda_unaryMachine_no_result_exists (t : Term) :
    ∃ (states : Nat) (p : Machine.Program states), ∀ n,
      (∀ m, ¬ NumericalResult t n m) ↔ (∀ m, ¬ Machine.Yields p n m) := by
  obtain ⟨states, p, h⟩ := lambda_unaryMachine_exists t
  exact ⟨states, p, fun n => by simp only [h n]⟩

#print axioms partrec_iff_unaryMachine
#print axioms lambdaComputable_iff_unaryMachine
#print axioms lambda_unaryMachine_exists
#print axioms unaryMachine_lambda_exists
end LambdaTuring
