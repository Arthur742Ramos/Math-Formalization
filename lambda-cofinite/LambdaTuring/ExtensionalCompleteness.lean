/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSTotalCompiler
public meta import LambdaTuring.CPSTotalCompiler
public import LambdaTuring.MachineExact
public meta import LambdaTuring.MachineExact
public import LambdaTuring.MathlibBridge
public meta import LambdaTuring.MathlibBridge
public import LambdaTuring.SubstTable
public meta import LambdaTuring.SubstTable

@[expose] public section

namespace LambdaTuring

/-- Unary partial recursiveness is exactly closed lambda numerical
    representability. The converse uses Mathlib's existential code theorem;
    it is not an executable extractor from a proof of partial recursiveness. -/
theorem lambdaComputable_iff_partrec (f : Nat →. Nat) :
    LambdaComputable f ↔ Nat.Partrec f := by
  constructor
  · rintro ⟨t, _, ht⟩
    have heq : numericalValue t = f := funext ht
    rw [← heq]
    exact numericalValue_partrec t
  · intro hf
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
    exact ⟨compileLambdaTotal c, by simpa [hc] using compileLambdaTotal_sound c⟩

/-- Every finite three-symbol table machine has a closed lambda representative
    with exactly its numerical observations. This is an existence theorem;
    it does not construct a machine-syntax-to-code translator. -/
theorem machine_lambda_exists {states : Nat} (p : Machine.Program states) :
    ∃ t, Scoped 0 t ∧ ∀ n m, NumericalResult t n m ↔ Machine.MathYields p n m := by
  obtain ⟨t, ht, hvalue⟩ := (lambdaComputable_iff_partrec (Machine.machineValue p)).2
    (Machine.machineValue_partrec p)
  refine ⟨t, ht, ?_⟩
  intro n m
  rw [← mem_numericalValue_iff, hvalue n, Machine.mem_machineValue_iff, Machine.math_yields_iff]

theorem machine_lambda_no_numerical_exists {states : Nat} (p : Machine.Program states) :
    ∃ t, Scoped 0 t ∧ ∀ n,
      (∀ m, ¬ NumericalResult t n m) ↔ (∀ m, ¬ Machine.MathYields p n m) := by
  obtain ⟨t, ht, h⟩ := machine_lambda_exists p
  refine ⟨t, ht, ?_⟩
  intro n
  simp only [h n]

/-- The same existence result applies to every Mathlib TM0 over this finite
    three-symbol alphabet and `Fin (states + 1)` state type. -/
theorem finite_mathlib_machine_lambda_exists {states : Nat}
    (p : Turing.TM0.Machine Machine.Symbol (Fin (states + 1))) :
    ∃ t, Scoped 0 t ∧ ∀ n m, NumericalResult t n m ↔
      ∃ output, output ∈ Turing.TM0.eval p (Machine.input n) ∧ Machine.mathDecode output = some m := by
  obtain ⟨t, ht, h⟩ := machine_lambda_exists (Machine.tableOfMathlib p)
  refine ⟨t, ht, ?_⟩
  intro n m
  simpa [Machine.MathYields, Machine.mathProgram_tableOfMathlib] using h n m

#print axioms lambdaComputable_iff_partrec
#print axioms machine_lambda_exists
#print axioms finite_mathlib_machine_lambda_exists

end LambdaTuring
