module

public import ErdosOverlap.Numerics.LeafIntegration

/-! Executable fixed-point bounds for rational polynomials and their integrals. -/

namespace ErdosOverlap.Numerics

open LeanCert.Core

@[expose] public section

def FixedBox.ofBounds (lo hi : ℚ) : FixedBox :=
  ⟨(FixedBox.ofRat lo).lo, (FixedBox.ofRat hi).hi⟩

theorem FixedBox.mem_ofBounds {lo hi : ℚ} {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) : x ∈ FixedBox.ofBounds lo hi := by
  exact ⟨(FixedBox.mem_ofRat lo).1.trans
      (mul_le_mul_of_nonneg_right hx.1 fixedScale_real_pos.le),
    (mul_le_mul_of_nonneg_right hx.2 fixedScale_real_pos.le).trans
      (FixedBox.mem_ofRat hi).2⟩

def polynomialBox (cs : List ℚ) (I : FixedBox) : FixedBox :=
  FixedBox.hornerBoxes I (cs.map FixedBox.ofRat)

theorem polynomial_mem_box (cs : List ℚ) {I : FixedBox} {x : ℝ} (hx : x ∈ I) :
    polynomialValue cs x ∈ polynomialBox cs I := by
  apply polynomialValue_mem_hornerBoxes hx
  induction cs with
  | nil => exact List.Forall₂.nil
  | cons c cs ih => exact List.Forall₂.cons (FixedBox.mem_ofRat c) ih

theorem polynomialRat_mem_box (cs : List ℚ) (x : ℚ) :
    (polynomialRatValue cs x : ℝ) ∈ polynomialBox cs (FixedBox.ofRat x) := by
  rw [polynomialRatValue_cast]
  exact polynomial_mem_box cs (FixedBox.mem_ofRat x)

def affineIntegralBox (cs : List ℚ) (alpha beta lo hi : ℚ) : FixedBox :=
  let first := (polynomialBox (primitiveCoeffs cs) (FixedBox.ofRat hi)).sub
    (polynomialBox (primitiveCoeffs cs) (FixedBox.ofRat lo))
  let second := (polynomialBox (weightedPrimitiveCoeffs cs) (FixedBox.ofRat hi)).sub
    (polynomialBox (weightedPrimitiveCoeffs cs) (FixedBox.ofRat lo))
  ((FixedBox.ofRat alpha).mul first).add ((FixedBox.ofRat beta).mul second)

theorem affineIntegral_mem_box (cs : List ℚ) (alpha beta lo hi : ℚ) :
    (affinePolynomialIntegralRat cs alpha beta lo hi : ℝ) ∈
      affineIntegralBox cs alpha beta lo hi := by
  unfold affinePolynomialIntegralRat affineIntegralBox
  push_cast
  exact FixedBox.mem_add
    (FixedBox.mem_mul (FixedBox.mem_ofRat alpha)
      (FixedBox.mem_sub (polynomialRat_mem_box _ hi) (polynomialRat_mem_box _ lo)))
    (FixedBox.mem_mul (FixedBox.mem_ofRat beta)
      (FixedBox.mem_sub (polynomialRat_mem_box _ hi) (polynomialRat_mem_box _ lo)))

def normalizedIntegralBox (cs : List ℚ)
    (alpha beta center radius lo hi : ℚ) : FixedBox :=
  (FixedBox.ofRat radius).mul (affineIntegralBox cs (alpha+beta*center) (beta*radius)
    ((lo-center)/radius) ((hi-center)/radius))

theorem normalizedIntegral_mem_box (cs : List ℚ)
    (alpha beta center radius lo hi : ℚ) :
    (normalizedPolynomialIntegralRat cs alpha beta center radius lo hi : ℝ) ∈
      normalizedIntegralBox cs alpha beta center radius lo hi := by
  unfold normalizedPolynomialIntegralRat normalizedIntegralBox
  push_cast
  exact FixedBox.mem_mul (FixedBox.mem_ofRat radius)
    (affineIntegral_mem_box cs _ _ _ _)

end
end ErdosOverlap.Numerics
