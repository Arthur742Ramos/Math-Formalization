/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCached

/-!
# Outer integral traces without an unused weighted primitive

Only the range and the two ordinary primitive values are needed for the
unweighted integral. The omitted weighted-primitive boxes may be arbitrary:
their multiplier is exactly zero in the original checked formula.
-/

namespace ErdosOverlap.Numerics

public section

theorem FixedBox.ofRat_zero_eq : FixedBox.ofRat 0 = ⟨0, 0⟩ := by
  decide +kernel

theorem FixedBox.ofRat_zero_mul (I : FixedBox) :
    (FixedBox.ofRat 0).mul I = FixedBox.ofRat 0 := by
  rw [FixedBox.ofRat_zero_eq]
  cases I
  simp only [FixedBox.mul, FixedBox.minProduct, FixedBox.maxProduct,
    zero_mul, min_self, max_self, neg_zero]
  rfl

theorem FixedBox.add_ofRat_zero (I : FixedBox) : I.add (FixedBox.ofRat 0) = I := by
  rw [FixedBox.ofRat_zero_eq]
  cases I
  simp only [FixedBox.add, add_zero]

@[expose] def CachedPolynomialTrace.checkBase (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi &&
  t.trace.range.checkExact t.inputs.range c.coefficients &&
  t.trace.primitiveLo.checkExact t.inputs.lo c.primitive &&
  t.trace.primitiveHi.checkExact t.inputs.hi c.primitive

theorem CachedPolynomialTrace.checkBase_results {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (hc : t.checkBase c p lo hi = true) :
    t.trace.range.result = c.rangeBox p lo hi ∧
    t.trace.primitiveLo.result = FixedBox.hornerBoxes
      (FixedBox.ofRat ((lo - p.center) / p.radius)) c.primitive ∧
    t.trace.primitiveHi.result = FixedBox.hornerBoxes
      (FixedBox.ofRat ((hi - p.center) / p.radius)) c.primitive := by
  simp only [checkBase, Bool.and_eq_true_iff] at hc
  have hI : t.inputs.range = p.normalizedBox lo hi ∧
      t.inputs.lo = FixedBox.ofRat ((lo - p.center) / p.radius) ∧
      t.inputs.hi = FixedBox.ofRat ((hi - p.center) / p.radius) :=
    of_decide_eq_true hc.1.1.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hI.1, PolynomialBoxCache.rangeBox] using
      HornerTrace.result_eq_of_exact hc.1.1.2
  · simpa only [hI.2.1] using HornerTrace.result_eq_of_exact hc.1.2
  · simpa only [hI.2.2] using HornerTrace.result_eq_of_exact hc.2

theorem CachedPolynomialTrace.integralBox_eq_of_base {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (hc : t.checkBase c p lo hi = true) :
    t.trace.integralBox p 1 0 = c.integralBox p 1 0 lo hi := by
  have hs := checkBase_results hc
  simp only [PolynomialBoxTrace.integralBox, PolynomialBoxCache.integralBox,
    zero_mul, add_zero, FixedBox.ofRat_zero_mul, FixedBox.add_ofRat_zero,
    hs.2.1, hs.2.2]

end
end ErdosOverlap.Numerics

namespace ErdosOverlap

open Numerics

public section

@[expose] def CachedOuterLeaf.checkBase (l : CachedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel)
    (caches : ℕ → PolynomialBoxCache) (count : ℕ) : Bool :=
  let m := models l.leaf.cell
  decide (l.leaf.cell < count ∧ 0 < m.radius ∧ l.leaf.left ≤ l.leaf.right ∧
    m.center - m.radius ≤ l.leaf.left ∧ l.leaf.right ≤ m.center + m.radius) &&
    l.cached.checkBase (caches l.leaf.cell) (m.polynomial p) l.leaf.left l.leaf.right &&
    (l.upperBox p models).upperBoundedBy l.leaf.bound

theorem CachedOuterLeaf.upperBox_eq_of_base
    {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache}
    (hc : (caches l.leaf.cell).check ((models l.leaf.cell).polynomial p) = true)
    (ht : l.cached.checkBase (caches l.leaf.cell) ((models l.leaf.cell).polynomial p)
      l.leaf.left l.leaf.right = true) :
    l.upperBox p models = ((models l.leaf.cell).polynomial p).positiveIntegralUpperBox
      l.leaf.left l.leaf.right (models l.leaf.cell).error := by
  have hs := CachedPolynomialTrace.checkBase_results ht
  simp only [upperBox, PolynomialPiece.positiveIntegralUpperBox,
    hs.1, PolynomialBoxCache.rangeBox_eq hc,
    CachedPolynomialTrace.integralBox_eq_of_base ht, PolynomialBoxCache.integralBox_eq hc]

theorem CachedOuterLeaf.checkBase_sound {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    (hc : l.checkBase p models caches count = true) : l.leaf.check p models count = true := by
  simp only [checkBase, Bool.and_eq_true_iff] at hc
  have hg := of_decide_eq_true hc.1.1
  have he := l.upperBox_eq_of_base (hcache l.leaf.cell hg.1) hc.1.2
  change decide (l.leaf.cell < count ∧ 0 < (models l.leaf.cell).radius ∧
      l.leaf.left ≤ l.leaf.right ∧
      (models l.leaf.cell).center - (models l.leaf.cell).radius ≤ l.leaf.left ∧
      l.leaf.right ≤ (models l.leaf.cell).center + (models l.leaf.cell).radius) &&
    ((models l.leaf.cell).polynomial p).positiveIntegralUpperCheck
      l.leaf.left l.leaf.right (models l.leaf.cell).error l.leaf.bound = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hc.1.1, ?_⟩
  change (((models l.leaf.cell).polynomial p).positiveIntegralUpperBox
    l.leaf.left l.leaf.right (models l.leaf.cell).error).upperBoundedBy l.leaf.bound = true
  rw [← he]
  exact hc.2

@[expose] def outerCachedChainCheckBase (p : OuterFourierPolynomial)
    (models : ℕ → OuterCellModel) (caches : ℕ → PolynomialBoxCache) (count : ℕ) :
    ℚ → ℚ → List CachedOuterLeaf → Bool
  | a, b, [] => decide (a = b)
  | a, b, l :: ls => decide (l.leaf.left = a) && l.checkBase p models caches count &&
      outerCachedChainCheckBase p models caches count l.leaf.right b ls

theorem outerChainCheck_of_cachedChainBase {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    {a b : ℚ} {leaves : List CachedOuterLeaf}
    (hc : outerCachedChainCheckBase p models caches count a b leaves = true) :
    outerChainCheck p models count a b (leaves.map CachedOuterLeaf.leaf) = true := by
  induction leaves generalizing a with
  | nil => exact hc
  | cons l ls ih =>
    change (decide (l.leaf.left = a) && l.checkBase p models caches count) &&
      outerCachedChainCheckBase p models caches count l.leaf.right b ls = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have hh := Bool.and_eq_true_iff.mp hs.1
    change (decide (l.leaf.left = a) && l.leaf.check p models count) &&
      outerChainCheck p models count l.leaf.right b (ls.map CachedOuterLeaf.leaf) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hh.1, l.checkBase_sound hcache hh.2⟩, ih hs.2⟩

end
end ErdosOverlap
