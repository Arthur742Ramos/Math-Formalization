/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCachedBase

/-!
# Width-five outer traces with literal normalized inputs

The width-five checkpoint checker verifies only the range and the two
ordinary primitive values needed for the unweighted integral. The omitted weighted-primitive boxes may be arbitrary:
their multiplier is exactly zero in the original checked formula.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def CachedPolynomialTrace.checkBaseFive (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi &&
  t.trace.range.check t.inputs.range c.coefficients &&
  t.trace.primitiveLo.check t.inputs.lo c.primitive &&
  t.trace.primitiveHi.check t.inputs.hi c.primitive

theorem CachedPolynomialTrace.checkBaseFive_results {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (hc : t.checkBaseFive c p lo hi = true) :
    t.trace.range.result = c.rangeBox p lo hi ∧
    t.trace.primitiveLo.result = FixedBox.hornerBoxes
      (FixedBox.ofRat ((lo - p.center) / p.radius)) c.primitive ∧
    t.trace.primitiveHi.result = FixedBox.hornerBoxes
      (FixedBox.ofRat ((hi - p.center) / p.radius)) c.primitive := by
  simp only [checkBaseFive, Bool.and_eq_true_iff] at hc
  have hI : t.inputs.range = p.normalizedBox lo hi ∧
      t.inputs.lo = FixedBox.ofRat ((lo - p.center) / p.radius) ∧
      t.inputs.hi = FixedBox.ofRat ((hi - p.center) / p.radius) :=
    of_decide_eq_true hc.1.1.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hI.1, PolynomialBoxCache.rangeBox] using
      HornerTrace.result_eq hc.1.1.2
  · simpa only [hI.2.1] using HornerTrace.result_eq hc.1.2
  · simpa only [hI.2.2] using HornerTrace.result_eq hc.2

theorem CachedPolynomialTrace.integralBox_eq_of_base_five {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (hc : t.checkBaseFive c p lo hi = true) :
    t.trace.integralBox p 1 0 = c.integralBox p 1 0 lo hi := by
  have hs := checkBaseFive_results hc
  simp only [PolynomialBoxTrace.integralBox, PolynomialBoxCache.integralBox,
    zero_mul, add_zero, FixedBox.ofRat_zero_mul, FixedBox.add_ofRat_zero,
    hs.2.1, hs.2.2]

end
end ErdosOverlap.Numerics

namespace ErdosOverlap

open Numerics

public section

@[expose] def CachedOuterLeaf.checkBaseFive (l : CachedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel)
    (caches : ℕ → PolynomialBoxCache) (count : ℕ) : Bool :=
  let m := models l.leaf.cell
  decide (l.leaf.cell < count ∧ 0 < m.radius ∧ l.leaf.left ≤ l.leaf.right ∧
    m.center - m.radius ≤ l.leaf.left ∧ l.leaf.right ≤ m.center + m.radius) &&
    l.cached.checkBaseFive (caches l.leaf.cell) (m.polynomial p) l.leaf.left l.leaf.right &&
    (l.upperBox p models).upperBoundedBy l.leaf.bound

theorem CachedOuterLeaf.upperBox_eq_of_base_five
    {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache}
    (hc : (caches l.leaf.cell).check ((models l.leaf.cell).polynomial p) = true)
    (ht : l.cached.checkBaseFive (caches l.leaf.cell) ((models l.leaf.cell).polynomial p)
      l.leaf.left l.leaf.right = true) :
    l.upperBox p models = ((models l.leaf.cell).polynomial p).positiveIntegralUpperBox
      l.leaf.left l.leaf.right (models l.leaf.cell).error := by
  have hs := CachedPolynomialTrace.checkBaseFive_results ht
  simp only [upperBox, PolynomialPiece.positiveIntegralUpperBox,
    hs.1, PolynomialBoxCache.rangeBox_eq hc,
    CachedPolynomialTrace.integralBox_eq_of_base_five ht, PolynomialBoxCache.integralBox_eq hc]

theorem CachedOuterLeaf.checkBaseFive_sound {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    (hc : l.checkBaseFive p models caches count = true) : l.leaf.check p models count = true := by
  simp only [checkBaseFive, Bool.and_eq_true_iff] at hc
  have hg := of_decide_eq_true hc.1.1
  have he := l.upperBox_eq_of_base_five (hcache l.leaf.cell hg.1) hc.1.2
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

@[expose] def outerCachedChainCheckBaseFive (p : OuterFourierPolynomial)
    (models : ℕ → OuterCellModel) (caches : ℕ → PolynomialBoxCache) (count : ℕ) :
    ℚ → ℚ → List CachedOuterLeaf → Bool
  | a, b, [] => decide (a = b)
  | a, b, l :: ls => decide (l.leaf.left = a) && l.checkBaseFive p models caches count &&
      outerCachedChainCheckBaseFive p models caches count l.leaf.right b ls

theorem outerChainCheck_of_cachedChainBaseFive {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    {a b : ℚ} {leaves : List CachedOuterLeaf}
    (hc : outerCachedChainCheckBaseFive p models caches count a b leaves = true) :
    outerChainCheck p models count a b (leaves.map CachedOuterLeaf.leaf) = true := by
  induction leaves generalizing a with
  | nil => exact hc
  | cons l ls ih =>
    change (decide (l.leaf.left = a) && l.checkBaseFive p models caches count) &&
      outerCachedChainCheckBaseFive p models caches count l.leaf.right b ls = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have hh := Bool.and_eq_true_iff.mp hs.1
    change (decide (l.leaf.left = a) && l.leaf.check p models count) &&
      outerChainCheck p models count l.leaf.right b (ls.map CachedOuterLeaf.leaf) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hh.1, l.checkBaseFive_sound hcache hh.2⟩, ih hs.2⟩

end
end ErdosOverlap
