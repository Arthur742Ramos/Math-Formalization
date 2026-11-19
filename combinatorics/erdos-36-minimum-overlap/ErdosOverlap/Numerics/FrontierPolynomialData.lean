/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativePolynomialPatch
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.FrontierGrid.Rows

namespace ErdosOverlap.Numerics
@[expose] public section

def addPolynomialCoefficients : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: addPolynomialCoefficients xs ys

theorem polynomialValue_addPolynomialCoefficients (xs ys : List ℚ) (u : ℝ) :
    polynomialValue (addPolynomialCoefficients xs ys) u =
      polynomialValue xs u + polynomialValue ys u := by
  induction xs generalizing ys with
  | nil => simp [addPolynomialCoefficients, polynomialValue]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addPolynomialCoefficients, polynomialValue]
    | cons y ys =>
      simp only [addPolynomialCoefficients, polynomialValue, Rat.cast_add, ih]
      ring

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.FrontierGrid
open Numerics
@[expose] public section

def combinedCoefficients (j : ℕ) : List ℚ :=
  addPolynomialCoefficients
    (quantizedCoefficients (Native6Grid.coefficientRow j))
    (quantizedCoefficients (coefficientRow j))

end
end ErdosOverlap.FrontierGrid
