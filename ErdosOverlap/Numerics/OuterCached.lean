/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCell
public import ErdosOverlap.Numerics.PolynomialInputCache

/-!
# Outer integral checks with cached inputs and exact Horner steps

Normalized-coordinate boxes and every integer floor/ceiling step are
checked. The adapter recovers the unchanged positive-integral and chain
checks, preserving all existing analytic source obligations.
-/

namespace ErdosOverlap

open Numerics

public section

structure CachedOuterLeaf where
  leaf : OuterIntegralLeaf
  cached : CachedPolynomialTrace
  deriving Repr

@[expose] def CachedOuterLeaf.upperBox (l : CachedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel) : FixedBox :=
  let m := models l.leaf.cell
  let line := l.cached.trace.range.result.positiveLine
  ((FixedBox.ofRat line.slope).mul
      (l.cached.trace.integralBox (m.polynomial p) 1 0)).add
    (FixedBox.ofRat (line.constant * (l.leaf.right - l.leaf.left) +
      m.error * (l.leaf.right - l.leaf.left)))

@[expose] def CachedOuterLeaf.check (l : CachedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel)
    (caches : ℕ → PolynomialBoxCache) (count : ℕ) : Bool :=
  let m := models l.leaf.cell
  decide (l.leaf.cell < count ∧ 0 < m.radius ∧ l.leaf.left ≤ l.leaf.right ∧
    m.center - m.radius ≤ l.leaf.left ∧ l.leaf.right ≤ m.center + m.radius) &&
    l.cached.check (caches l.leaf.cell) (m.polynomial p) l.leaf.left l.leaf.right &&
    (l.upperBox p models).upperBoundedBy l.leaf.bound

theorem CachedOuterLeaf.upperBox_eq {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache}
    (hc : (caches l.leaf.cell).check ((models l.leaf.cell).polynomial p) = true)
    (ht : l.cached.check (caches l.leaf.cell) ((models l.leaf.cell).polynomial p)
      l.leaf.left l.leaf.right = true) :
    l.upperBox p models = ((models l.leaf.cell).polynomial p).positiveIntegralUpperBox
      l.leaf.left l.leaf.right (models l.leaf.cell).error := by
  have he := CachedPolynomialTrace.check_sound ht
  simp only [upperBox, PolynomialPiece.positiveIntegralUpperBox,
    l.cached.trace.range_eq_of_exact he, PolynomialBoxCache.rangeBox_eq hc,
    l.cached.trace.integralBox_eq_of_exact he, PolynomialBoxCache.integralBox_eq hc]

theorem CachedOuterLeaf.check_sound {l : CachedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    (hc : l.check p models caches count = true) : l.leaf.check p models count = true := by
  simp only [check, Bool.and_eq_true_iff] at hc
  have hg := of_decide_eq_true hc.1.1
  have he := l.upperBox_eq (hcache l.leaf.cell hg.1) hc.1.2
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

@[expose] def outerCachedChainCheck (p : OuterFourierPolynomial)
    (models : ℕ → OuterCellModel) (caches : ℕ → PolynomialBoxCache) (count : ℕ) :
    ℚ → ℚ → List CachedOuterLeaf → Bool
  | a, b, [] => decide (a = b)
  | a, b, l :: ls => decide (l.leaf.left = a) && l.check p models caches count &&
      outerCachedChainCheck p models caches count l.leaf.right b ls

theorem outerChainCheck_of_cachedChain {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    {a b : ℚ} {leaves : List CachedOuterLeaf}
    (hc : outerCachedChainCheck p models caches count a b leaves = true) :
    outerChainCheck p models count a b (leaves.map CachedOuterLeaf.leaf) = true := by
  induction leaves generalizing a with
  | nil => exact hc
  | cons l ls ih =>
    change (decide (l.leaf.left = a) && l.check p models caches count) &&
      outerCachedChainCheck p models caches count l.leaf.right b ls = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have hh := Bool.and_eq_true_iff.mp hs.1
    change (decide (l.leaf.left = a) && l.leaf.check p models count) &&
      outerChainCheck p models count l.leaf.right b (ls.map CachedOuterLeaf.leaf) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hh.1, l.check_sound hcache hh.2⟩, ih hs.2⟩

end
end ErdosOverlap
