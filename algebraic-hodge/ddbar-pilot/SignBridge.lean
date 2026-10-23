module

public import Representative

/-!
# The sign twist on actual bicomplex operators

Twisting the vertical maps in a commuting mathlib bicomplex gives
anticommuting operators. This file does not construct a categorical equivalence
from an independently defined category of Dolbeault double complexes.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicHodgePilot

variable {k : Type} [Field k] (K : Bicomplex k)

/-- Vertical differential with the standard column sign. -/
def signedVertical (p q : ℤ) := (p.negOnePow : ℤ) • vertical K p q

theorem signedVertical_anticommute (p q : ℤ) (x : (K.X p).X q) :
    horizontal K p (q + 1) (signedVertical K p q x) +
      signedVertical K (p + 1) q (horizontal K p q x) = 0 := by
  have hc := congrArg (fun f => f.hom x) (K.d_comm p (p + 1) q (q + 1))
  change vertical K (p + 1) q (horizontal K p q x) =
    horizontal K p (q + 1) (vertical K p q x) at hc
  simp [signedVertical, Int.negOnePow_succ, hc]

theorem sign_twist_involutive (p q : ℤ) :
    (p.negOnePow : ℤ) • signedVertical K p q = vertical K p q := by
  simp [signedVertical, smul_smul, ← Units.val_mul, Int.units_mul_self]

theorem signedVertical_squared (p q : ℤ) (x : (K.X p).X q) :
    signedVertical K p (q + 1) (signedVertical K p q x) = 0 := by
  have hv := congrArg (fun f => f.hom x) ((K.X p).d_comp_d q (q + 1) (q + 1 + 1))
  change vertical K p (q + 1) (vertical K p q x) = 0 at hv
  simp [signedVertical, hv]

theorem signedVertical_ker (p q : ℤ) :
    LinearMap.ker (signedVertical K p q) = LinearMap.ker (vertical K p q) := by
  ext x
  constructor
  · intro hx
    have h := congrArg (fun y => (p.negOnePow : ℤ) • y) hx
    simpa [signedVertical, smul_smul, ← Units.val_mul, Int.units_mul_self] using h
  · intro hx
    change signedVertical K p q x = 0
    simp [signedVertical, LinearMap.mem_ker.mp hx]

theorem signedVertical_range (p q : ℤ) :
    LinearMap.range (signedVertical K p q) = LinearMap.range (vertical K p q) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(p.negOnePow : ℤ) • x, by simp [signedVertical]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(p.negOnePow : ℤ) • x, ?_⟩
    simp [signedVertical, smul_smul, ← Units.val_mul, Int.units_mul_self]

end AlgebraicHodgePilot
