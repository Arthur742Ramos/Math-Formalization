/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterBasis

/-!
# Exact integer assembly of shared outer trigonometric models

Source weights share an integer denominator `D`, and the local polynomial
basis shares an integer denominator `S`. Their weighted coefficient sum can
therefore be checked entirely with integers and decoded once at denominator
`D*S`. The identities are exact, including the lookup's empty default case.
-/

@[expose] public section

namespace ErdosOverlap.Numerics

structure IntTrigTerm where
  frequency : ℚ
  weight : ℤ
  deriving DecidableEq, Repr

structure IntLocalTrigApprox where
  frequency : ℚ
  cosineCoefficients : List ℤ
  sineCoefficients : List ℤ
  error : ℚ
  deriving DecidableEq, Repr

def decodeCoefficients (S : ℤ) (cs : List ℤ) : List ℚ :=
  cs.map (fun (z : ℤ) => (z : ℚ)/(S : ℚ))

def IntTrigTerm.decode (D : ℤ) (t : IntTrigTerm) : CosineTerm :=
  ⟨t.frequency, (t.weight : ℚ)/(D : ℚ)⟩

def decodeTerms (D : ℤ) (ts : List IntTrigTerm) : List CosineTerm :=
  ts.map (IntTrigTerm.decode D)

def IntLocalTrigApprox.decode (S : ℤ) (a : IntLocalTrigApprox) : LocalTrigApprox :=
  ⟨a.frequency, decodeCoefficients S a.cosineCoefficients,
    decodeCoefficients S a.sineCoefficients, a.error⟩

def decodeBasis (S : ℤ) (bs : List IntLocalTrigApprox) : List LocalTrigApprox :=
  bs.map (IntLocalTrigApprox.decode S)

def addIntegerCoefficients : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: addIntegerCoefficients xs ys

def scaleIntegerCoefficients (w : ℤ) (cs : List ℤ) : List ℤ := cs.map (w * ·)

def integerLookup (frequency : ℚ) : List IntLocalTrigApprox → IntLocalTrigApprox
  | [] => ⟨frequency, [], [], 1⟩
  | a :: as => if frequency = a.frequency then a else integerLookup frequency as

def integerCompile (sine : Bool) (basis : List IntLocalTrigApprox) :
    List IntTrigTerm → List ℤ
  | [] => []
  | a :: as =>
    let b := integerLookup a.frequency basis
    addIntegerCoefficients
      (scaleIntegerCoefficients a.weight (if sine then b.sineCoefficients else b.cosineCoefficients))
      (integerCompile sine basis as)

theorem decodeCoefficients_add (S : ℤ) (xs ys : List ℤ) :
    addPolynomialCoefficients (decodeCoefficients S xs) (decodeCoefficients S ys) =
      decodeCoefficients S (addIntegerCoefficients xs ys) := by
  induction xs generalizing ys with
  | nil => simp [decodeCoefficients, addIntegerCoefficients, addPolynomialCoefficients]
  | cons x xs ih =>
    cases ys with
    | nil => simp [decodeCoefficients, addIntegerCoefficients, addPolynomialCoefficients]
    | cons y ys =>
      simp only [decodeCoefficients, List.map_cons, addIntegerCoefficients,
        addPolynomialCoefficients, Int.cast_add, add_div]
      exact congrArg (List.cons ((x : ℚ)/(S : ℚ)+(y : ℚ)/(S : ℚ))) (ih ys)

theorem decodeCoefficients_scale (D S w : ℤ) (cs : List ℤ) :
    scalePolynomialCoefficients ((w : ℚ)/(D : ℚ)) (decodeCoefficients S cs) =
      decodeCoefficients (D*S) (scaleIntegerCoefficients w cs) := by
  induction cs with
  | nil => simp [scalePolynomialCoefficients, decodeCoefficients, scaleIntegerCoefficients]
  | cons c cs ih =>
    simp only [scalePolynomialCoefficients, scaleIntegerCoefficients, decodeCoefficients,
      List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [Int.cast_mul, div_mul_div_comm]

theorem localTrigLookup_decode (S : ℤ) (frequency : ℚ) (basis : List IntLocalTrigApprox) :
    localTrigLookup frequency (decodeBasis S basis) =
      (integerLookup frequency basis).decode S := by
  induction basis with
  | nil => rfl
  | cons a as ih =>
    simp only [decodeBasis, List.map_cons, localTrigLookup, integerLookup, IntLocalTrigApprox.decode]
    by_cases h : frequency = a.frequency
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      exact ih

/-- Exact common-denominator compilation. The identity is valid even when
one denominator is zero, using the total field division convention. -/
theorem compileTrigCoefficients_decode (sine : Bool) (D S : ℤ)
    (basis : List IntLocalTrigApprox) (terms : List IntTrigTerm) :
    compileTrigCoefficients sine (decodeBasis S basis) (decodeTerms D terms) =
      decodeCoefficients (D*S) (integerCompile sine basis terms) := by
  induction terms with
  | nil => rfl
  | cons a as ih =>
    simp only [decodeTerms, List.map_cons, compileTrigCoefficients, IntTrigTerm.decode]
    rw [localTrigLookup_decode]
    change addPolynomialCoefficients
      (scalePolynomialCoefficients ((a.weight : ℚ)/(D : ℚ))
        (if sine then decodeCoefficients S (integerLookup a.frequency basis).sineCoefficients
          else decodeCoefficients S (integerLookup a.frequency basis).cosineCoefficients))
      (compileTrigCoefficients sine (decodeBasis S basis) (decodeTerms D as)) = _
    rw [ih]
    cases sine <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      decodeCoefficients_scale, decodeCoefficients_add, integerCompile]

theorem compileTrigCoefficients_add_decode (D S : ℤ)
    (basis : List IntLocalTrigApprox) (cosineTerms sineTerms : List IntTrigTerm) :
    addPolynomialCoefficients
        (compileTrigCoefficients false (decodeBasis S basis) (decodeTerms D cosineTerms))
        (compileTrigCoefficients true (decodeBasis S basis) (decodeTerms D sineTerms)) =
      decodeCoefficients (D*S)
        (addIntegerCoefficients (integerCompile false basis cosineTerms)
          (integerCompile true basis sineTerms)) := by
  rw [compileTrigCoefficients_decode, compileTrigCoefficients_decode, decodeCoefficients_add]

def integerCompileCheck (sine : Bool) (basis : List IntLocalTrigApprox)
    (terms : List IntTrigTerm) (result : List ℤ) : Bool :=
  decide (integerCompile sine basis terms = result)

theorem integerCompileCheck_sound {sine : Bool} {basis : List IntLocalTrigApprox}
    {terms : List IntTrigTerm} {result : List ℤ} (D S : ℤ)
    (hc : integerCompileCheck sine basis terms result = true) :
    compileTrigCoefficients sine (decodeBasis S basis) (decodeTerms D terms) =
      decodeCoefficients (D*S) result := by
  rw [compileTrigCoefficients_decode, (of_decide_eq_true hc : integerCompile sine basis terms = result)]

def integerCompileSumCheck (basis : List IntLocalTrigApprox)
    (cosineTerms sineTerms : List IntTrigTerm) (result : List ℤ) : Bool :=
  decide (addIntegerCoefficients (integerCompile false basis cosineTerms)
    (integerCompile true basis sineTerms) = result)

theorem integerCompileSumCheck_sound {basis : List IntLocalTrigApprox}
    {cosineTerms sineTerms : List IntTrigTerm} {result : List ℤ} (D S : ℤ)
    (hc : integerCompileSumCheck basis cosineTerms sineTerms result = true) :
    addPolynomialCoefficients
        (compileTrigCoefficients false (decodeBasis S basis) (decodeTerms D cosineTerms))
        (compileTrigCoefficients true (decodeBasis S basis) (decodeTerms D sineTerms)) =
      decodeCoefficients (D*S) result := by
  rw [compileTrigCoefficients_add_decode,
    (of_decide_eq_true hc : addIntegerCoefficients (integerCompile false basis cosineTerms)
      (integerCompile true basis sineTerms) = result)]

end ErdosOverlap.Numerics
