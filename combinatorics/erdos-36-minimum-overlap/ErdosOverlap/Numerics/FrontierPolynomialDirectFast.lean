/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.

Exact fixed-point Horner evaluation.
-/
module

public import ErdosOverlap.Numerics.FixedBoxFast
public import ErdosOverlap.Numerics.FrontierPolynomialDirectTrace

namespace ErdosOverlap.Numerics

@[expose] public section

def FixedBox.hornerBoxesFast (I : FixedBox) : List FixedBox → FixedBox
  | [] => FixedBox.ofRat 0
  | c :: cs => c.add (I.mulFast (FixedBox.hornerBoxesFast I cs))

theorem FixedBox.hornerBoxesFast_eq (I : FixedBox) (cs : List FixedBox) :
    FixedBox.hornerBoxesFast I cs = FixedBox.hornerBoxes I cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [FixedBox.hornerBoxesFast, FixedBox.hornerBoxes, ih,
      FixedBox.mulFast_eq_mul]

namespace FixedBox

private theorem mul_endpoints_ordered (I J : FixedBox) : (I.mul J).lo ≤ (I.mul J).hi := by
  have hp : I.minProduct J ≤ I.maxProduct J := by
    calc
      I.minProduct J ≤ min (I.lo * J.lo) (I.lo * J.hi) := min_le_left _ _
      _ ≤ I.lo * J.lo := min_le_left _ _
      _ ≤ max (I.lo * J.lo) (I.lo * J.hi) := le_max_left _ _
      _ ≤ I.maxProduct J := le_max_left _ _
  have hs := (floor_div_mul_le (I.minProduct J)).trans (hp.trans (le_ceil_div_mul (I.maxProduct J)))
  exact le_of_mul_le_mul_right hs fixedScale_pos

private theorem horner_endpoints_ordered (I : FixedBox) (cs : List FixedBox)
    (hcs : ∀ c ∈ cs, c.lo ≤ c.hi) : (hornerBoxes I cs).lo ≤ (hornerBoxes I cs).hi := by
  cases cs with
  | nil =>
    change (ofRat 0).lo ≤ (ofRat 0).hi
    decide +kernel
  | cons c cs =>
    exact add_le_add (hcs c (by simp)) (mul_endpoints_ordered I (hornerBoxes I cs))

def pointProduct (x : ℤ) (nonneg : Bool) (J : FixedBox) : FixedBox :=
  if nonneg then roundProductsShift (x * J.lo) (x * J.hi)
  else roundProductsShift (x * J.hi) (x * J.lo)

theorem pointProduct_eq (x : ℤ) (J : FixedBox) (ordered : J.lo ≤ J.hi) :
    pointProduct x (decide (0 ≤ x)) J = (⟨x, x⟩ : FixedBox).mul J := by
  by_cases hx : 0 ≤ x
  · have h := mul_le_mul_of_nonneg_left ordered hx
    simp only [pointProduct, ite_eq_left (decide_eq_true hx), roundProductsShift_eq, roundProducts,
      mul, minProduct, maxProduct, min_eq_left h, max_eq_right h, min_self, max_self]
  · have h := mul_le_mul_of_nonpos_left ordered (le_of_lt (lt_of_not_ge hx))
    have hfalse : ¬ (decide (0 ≤ x) = true) := fun htrue => hx (of_decide_eq_true htrue)
    simp only [pointProduct, ite_eq_right hfalse,
      roundProductsShift_eq, roundProducts, mul, minProduct, maxProduct,
      min_eq_right h, max_eq_left h, min_self, max_self]

def hornerPoint (x : ℤ) (nonneg : Bool) : List FixedBox → FixedBox
  | [] => ⟨0, 0⟩
  | c :: cs => c.add (pointProduct x nonneg (hornerPoint x nonneg cs))

theorem hornerPoint_eq (x : ℤ) (cs : List FixedBox) (hcs : ∀ c ∈ cs, c.lo ≤ c.hi) :
    hornerPoint x (decide (0 ≤ x)) cs = hornerBoxes ⟨x,x⟩ cs := by
  induction cs with
  | nil =>
    change (⟨0, 0⟩ : FixedBox) = ofRat 0
    decide +kernel
  | cons c cs ih =>
    have ht : ∀ d ∈ cs, d.lo ≤ d.hi := fun d hd => hcs d (List.mem_cons_of_mem _ hd)
    simp only [hornerPoint, hornerBoxes, ih ht,
      pointProduct_eq x _ (horner_endpoints_ordered ⟨x,x⟩ cs ht)]

def hornerBoxesPoint (I : FixedBox) (cs : List FixedBox) : FixedBox :=
  if I.lo = I.hi ∧ cs.all (fun c => decide (c.lo ≤ c.hi)) = true then
    hornerPoint I.lo (decide (0 ≤ I.lo)) cs
  else hornerBoxesFast I cs

theorem hornerBoxesPoint_eq (I : FixedBox) (cs : List FixedBox) :
    hornerBoxesPoint I cs = hornerBoxesFast I cs := by
  unfold hornerBoxesPoint
  split
  · rename_i h
    have hcs : ∀ c ∈ cs, c.lo ≤ c.hi := fun c hc =>
      of_decide_eq_true ((List.all_eq_true.mp h.2) c hc)
    rw [hornerPoint_eq _ _ hcs, hornerBoxesFast_eq]
    cases I with
    | mk lo hi =>
      have he : lo = hi := h.1
      subst hi
      rfl
  · rfl


end FixedBox

def CachedPolynomialTrace.directCheckFast (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi && decide (
    t.trace.range.result = FixedBox.hornerBoxesPoint t.inputs.range c.coefficients ∧
    t.trace.primitiveLo.result = FixedBox.hornerBoxesPoint t.inputs.lo c.primitive ∧
    t.trace.primitiveHi.result = FixedBox.hornerBoxesPoint t.inputs.hi c.primitive ∧
    t.trace.weightedLo.result = FixedBox.hornerBoxesPoint t.inputs.lo c.weightedPrimitive ∧
    t.trace.weightedHi.result = FixedBox.hornerBoxesPoint t.inputs.hi c.weightedPrimitive)

theorem CachedPolynomialTrace.directCheckFast_eq (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) :
    t.directCheckFast c p lo hi = t.directCheck c p lo hi := by
  simp only [CachedPolynomialTrace.directCheckFast,
    CachedPolynomialTrace.directCheck, FixedBox.hornerBoxesPoint_eq, FixedBox.hornerBoxesFast_eq]

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.FrontierLeaves

open Numerics
@[expose] public section

def Geometry.directTraceCheckFast (g : Geometry) (ca cb : PolynomialBoxCache)
    (ta tb : CachedPolynomialTrace) : Bool :=
  decide g.Valid &&
    ta.directCheckFast ca g.patchA g.left g.right &&
    tb.directCheckFast cb g.patchB g.left g.right &&
    g.cache.tracedCheck ta.trace tb.trace g.patchA g.patchB

theorem Geometry.directTraceCheckFast_eq (g : Geometry)
    (ca cb : PolynomialBoxCache) (ta tb : CachedPolynomialTrace) :
    g.directTraceCheckFast ca cb ta tb = g.directTraceCheck ca cb ta tb := by
  simp only [Geometry.directTraceCheckFast, Geometry.directTraceCheck,
    CachedPolynomialTrace.directCheckFast_eq]

end
end ErdosOverlap.FrontierLeaves
