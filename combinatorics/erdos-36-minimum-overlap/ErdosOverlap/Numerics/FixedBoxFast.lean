/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FixedBox
public import Init.Data.Int.Bitwise.Lemmas

/-!
# Sign-aware exact fixed-point interval multiplication

Eight of the nine sign combinations of ordered intervals require only two
corner products. The mixed/mixed case requires four. Invalid interval data
falls back to the original operation, so equivalence holds unconditionally.
-/

@[expose] public section

namespace ErdosOverlap.Numerics.FixedBox

def roundProducts (lo hi : ℤ) : FixedBox :=
  ⟨lo/fixedScale, -((-hi)/fixedScale)⟩

private theorem fixedScale_eq_pow : (((2 : ℕ) ^ 128 : ℕ) : ℤ) = fixedScale := by
  decide +kernel

def roundProductsShift (lo hi : ℤ) : FixedBox :=
  ⟨lo >>> (128 : ℕ), -((-hi) >>> (128 : ℕ))⟩

theorem roundProductsShift_eq (lo hi : ℤ) :
    roundProductsShift lo hi = roundProducts lo hi := by
  simp only [roundProductsShift, roundProducts, Int.shiftRight_eq_div_pow, fixedScale_eq_pow]

def mulFast (I J : FixedBox) : FixedBox :=
  if I.lo ≤ I.hi ∧ J.lo ≤ J.hi then
    if 0 ≤ I.lo then
      if 0 ≤ J.lo then roundProductsShift (I.lo*J.lo) (I.hi*J.hi)
      else if J.hi ≤ 0 then roundProductsShift (I.hi*J.lo) (I.lo*J.hi)
      else roundProductsShift (I.hi*J.lo) (I.hi*J.hi)
    else if I.hi ≤ 0 then
      if 0 ≤ J.lo then roundProductsShift (I.lo*J.hi) (I.hi*J.lo)
      else if J.hi ≤ 0 then roundProductsShift (I.hi*J.hi) (I.lo*J.lo)
      else roundProductsShift (I.lo*J.hi) (I.lo*J.lo)
    else
      if 0 ≤ J.lo then roundProductsShift (I.lo*J.hi) (I.hi*J.hi)
      else if J.hi ≤ 0 then roundProductsShift (I.hi*J.lo) (I.lo*J.lo)
      else roundProductsShift (min (I.lo*J.hi) (I.hi*J.lo))
        (max (I.lo*J.lo) (I.hi*J.hi))
  else I.mul J

private theorem products_nonneg {I J : FixedBox}
    (hI : I.lo ≤ I.hi) (hJ : J.lo ≤ J.hi) (hlo : 0 ≤ I.lo) :
    I.minProduct J = min (I.lo*J.lo) (I.hi*J.lo) ∧
      I.maxProduct J = max (I.lo*J.hi) (I.hi*J.hi) := by
  have hhi := hlo.trans hI
  simp only [minProduct, maxProduct,
    min_eq_left (mul_le_mul_of_nonneg_left hJ hlo),
    min_eq_left (mul_le_mul_of_nonneg_left hJ hhi),
    max_eq_right (mul_le_mul_of_nonneg_left hJ hlo),
    max_eq_right (mul_le_mul_of_nonneg_left hJ hhi), and_self]

private theorem products_nonpos {I J : FixedBox}
    (hI : I.lo ≤ I.hi) (hJ : J.lo ≤ J.hi) (hhi : I.hi ≤ 0) :
    I.minProduct J = min (I.lo*J.hi) (I.hi*J.hi) ∧
      I.maxProduct J = max (I.lo*J.lo) (I.hi*J.lo) := by
  have hlo := hI.trans hhi
  simp only [minProduct, maxProduct,
    min_eq_right (mul_le_mul_of_nonpos_left hJ hlo),
    min_eq_right (mul_le_mul_of_nonpos_left hJ hhi),
    max_eq_left (mul_le_mul_of_nonpos_left hJ hlo),
    max_eq_left (mul_le_mul_of_nonpos_left hJ hhi), and_self]

private theorem products_mixed {I J : FixedBox}
    (hJ : J.lo ≤ J.hi) (hlo : I.lo ≤ 0) (hhi : 0 ≤ I.hi) :
    I.minProduct J = min (I.lo*J.hi) (I.hi*J.lo) ∧
      I.maxProduct J = max (I.lo*J.lo) (I.hi*J.hi) := by
  simp only [minProduct, maxProduct,
    min_eq_right (mul_le_mul_of_nonpos_left hJ hlo),
    min_eq_left (mul_le_mul_of_nonneg_left hJ hhi),
    max_eq_left (mul_le_mul_of_nonpos_left hJ hlo),
    max_eq_right (mul_le_mul_of_nonneg_left hJ hhi), and_self]

/-- The optimized operation is exactly the original interval operation,
including on invalid boxes. No interval-validity premise is required. -/
theorem mulFast_eq_mul (I J : FixedBox) : I.mulFast J = I.mul J := by
  unfold mulFast
  by_cases hv : I.lo ≤ I.hi ∧ J.lo ≤ J.hi
  · rw [ite_eq_left hv]
    obtain ⟨hI,hJ⟩ := hv
    by_cases hIp : 0 ≤ I.lo
    · rw [ite_eq_left hIp]
      obtain ⟨hmin,hmax⟩ := products_nonneg hI hJ hIp
      by_cases hJp : 0 ≤ J.lo
      · rw [ite_eq_left hJp]
        have hJhi := hJp.trans hJ
        simp only [mul, hmin, hmax,
          min_eq_left (mul_le_mul_of_nonneg_right hI hJp),
          max_eq_right (mul_le_mul_of_nonneg_right hI hJhi), roundProductsShift_eq, roundProducts]
      · rw [ite_eq_right hJp]
        have hJlo : J.lo ≤ 0 := le_of_not_ge hJp
        by_cases hJn : J.hi ≤ 0
        · rw [ite_eq_left hJn]
          simp only [mul, hmin, hmax,
            min_eq_right (mul_le_mul_of_nonpos_right hI hJlo),
            max_eq_left (mul_le_mul_of_nonpos_right hI hJn), roundProductsShift_eq, roundProducts]
        · rw [ite_eq_right hJn]
          have hJhi : 0 ≤ J.hi := le_of_not_ge hJn
          simp only [mul, hmin, hmax,
            min_eq_right (mul_le_mul_of_nonpos_right hI hJlo),
            max_eq_right (mul_le_mul_of_nonneg_right hI hJhi), roundProductsShift_eq, roundProducts]
    · rw [ite_eq_right hIp]
      have hIlo : I.lo ≤ 0 := le_of_not_ge hIp
      by_cases hIn : I.hi ≤ 0
      · rw [ite_eq_left hIn]
        obtain ⟨hmin,hmax⟩ := products_nonpos hI hJ hIn
        by_cases hJp : 0 ≤ J.lo
        · rw [ite_eq_left hJp]
          have hJhi := hJp.trans hJ
          simp only [mul, hmin, hmax,
            min_eq_left (mul_le_mul_of_nonneg_right hI hJhi),
            max_eq_right (mul_le_mul_of_nonneg_right hI hJp), roundProductsShift_eq, roundProducts]
        · rw [ite_eq_right hJp]
          have hJlo : J.lo ≤ 0 := le_of_not_ge hJp
          by_cases hJn : J.hi ≤ 0
          · rw [ite_eq_left hJn]
            simp only [mul, hmin, hmax,
              min_eq_right (mul_le_mul_of_nonpos_right hI hJn),
              max_eq_left (mul_le_mul_of_nonpos_right hI hJlo), roundProductsShift_eq, roundProducts]
          · rw [ite_eq_right hJn]
            have hJhi : 0 ≤ J.hi := le_of_not_ge hJn
            simp only [mul, hmin, hmax,
              min_eq_left (mul_le_mul_of_nonneg_right hI hJhi),
              max_eq_left (mul_le_mul_of_nonpos_right hI hJlo), roundProductsShift_eq, roundProducts]
      · rw [ite_eq_right hIn]
        have hIhi : 0 ≤ I.hi := le_of_not_ge hIn
        obtain ⟨hmin,hmax⟩ := products_mixed hJ hIlo hIhi
        by_cases hJp : 0 ≤ J.lo
        · rw [ite_eq_left hJp]
          have hJhi := hJp.trans hJ
          have hmin' : I.lo*J.hi ≤ I.hi*J.lo :=
            (mul_nonpos_of_nonpos_of_nonneg hIlo hJhi).trans (mul_nonneg hIhi hJp)
          have hmax' : I.lo*J.lo ≤ I.hi*J.hi :=
            (mul_nonpos_of_nonpos_of_nonneg hIlo hJp).trans (mul_nonneg hIhi hJhi)
          simp only [mul, hmin, hmax, min_eq_left hmin', max_eq_right hmax', roundProductsShift_eq, roundProducts]
        · rw [ite_eq_right hJp]
          have hJlo : J.lo ≤ 0 := le_of_not_ge hJp
          by_cases hJn : J.hi ≤ 0
          · rw [ite_eq_left hJn]
            have hmin' : I.hi*J.lo ≤ I.lo*J.hi :=
              (mul_nonpos_of_nonneg_of_nonpos hIhi hJlo).trans
                (mul_nonneg_of_nonpos_of_nonpos hIlo hJn)
            have hmax' : I.hi*J.hi ≤ I.lo*J.lo :=
              (mul_nonpos_of_nonneg_of_nonpos hIhi hJn).trans
                (mul_nonneg_of_nonpos_of_nonpos hIlo hJlo)
            simp only [mul, hmin, hmax, min_eq_right hmin', max_eq_left hmax', roundProductsShift_eq, roundProducts]
          · rw [ite_eq_right hJn]
            simp only [mul, hmin, hmax, roundProductsShift_eq, roundProducts]
  · rw [ite_eq_right hv]

theorem mem_mulFast {x y : ℝ} {I J : FixedBox} (hx : x ∈ I) (hy : y ∈ J) :
    x*y ∈ I.mulFast J := by
  rw [mulFast_eq_mul]
  exact mem_mul hx hy

end ErdosOverlap.Numerics.FixedBox
