/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.IntegerOuterBasis
public import ErdosOverlap.Numerics.OuterCell

/-!
# Source bindings for exact integer outer compilation

The fieldwise checks below bind the integer representation to the already
proved rational basis and source terms.  Their soundness is ordinary list
induction; no generated coefficient table is trusted.
-/

namespace ErdosOverlap.Numerics

@[expose] public section

def LocalTrigApprox.sameCheck (a b : LocalTrigApprox) : Bool :=
  decide (a.frequency = b.frequency ∧ a.cosineCoefficients = b.cosineCoefficients ∧
    a.sineCoefficients = b.sineCoefficients ∧ a.error = b.error)

theorem LocalTrigApprox.sameCheck_sound {a b : LocalTrigApprox}
    (h : a.sameCheck b = true) : a = b := by
  cases a
  cases b
  simp only [sameCheck, decide_eq_true_eq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

def localTrigListCheck : List LocalTrigApprox → List LocalTrigApprox → Bool
  | [], [] => true
  | a :: as, b :: bs => a.sameCheck b && localTrigListCheck as bs
  | _, _ => false

theorem localTrigListCheck_sound {as bs : List LocalTrigApprox}
    (h : localTrigListCheck as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [localTrigListCheck, Bool.false_eq_true] at h
  | cons a as ih =>
    cases bs with
    | nil => simp only [localTrigListCheck, Bool.false_eq_true] at h
    | cons b bs =>
      have hh := Bool.and_eq_true_iff.mp h
      rw [LocalTrigApprox.sameCheck_sound hh.1, ih hh.2]

def CosineTerm.sameCheck (a b : CosineTerm) : Bool :=
  decide (a.frequency = b.frequency ∧ a.weight = b.weight)

theorem CosineTerm.sameCheck_sound {a b : CosineTerm}
    (h : a.sameCheck b = true) : a = b := by
  cases a
  cases b
  simp only [sameCheck, decide_eq_true_eq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

def trigTermListCheck : List CosineTerm → List CosineTerm → Bool
  | [], [] => true
  | a :: as, b :: bs => a.sameCheck b && trigTermListCheck as bs
  | _, _ => false

theorem trigTermListCheck_sound {as bs : List CosineTerm}
    (h : trigTermListCheck as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [trigTermListCheck, Bool.false_eq_true] at h
  | cons a as ih =>
    cases bs with
    | nil => simp only [trigTermListCheck, Bool.false_eq_true] at h
    | cons b bs =>
      have hh := Bool.and_eq_true_iff.mp h
      rw [CosineTerm.sameCheck_sound hh.1, ih hh.2]

/-- A checked integer sum gives the exact rational coefficient list of the
specified source polynomial, after independently checked source bindings. -/
theorem OuterFourierPolynomial.compiledCoefficients_eq_integer
    (p : ErdosOverlap.OuterFourierPolynomial) (D S : ℤ)
    {ib : List IntLocalTrigApprox} {basis : List LocalTrigApprox}
    {cosineTerms sineTerms : List IntTrigTerm} {result : List ℤ}
    (hb : decodeBasis S ib = basis)
    (hc : decodeTerms D cosineTerms = p.cosineTerms)
    (hs : decodeTerms D sineTerms = p.sineTerms)
    (hcheck : integerCompileSumCheck ib cosineTerms sineTerms result = true) :
    p.compiledCoefficients basis = decodeCoefficients (D*S) result := by
  rw [ErdosOverlap.OuterFourierPolynomial.compiledCoefficients, ← hb, ← hc, ← hs]
  exact integerCompileSumCheck_sound D S hcheck

end
end ErdosOverlap.Numerics
