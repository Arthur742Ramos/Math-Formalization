/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCell
public import ErdosOverlap.Numerics.PolynomialBoxTrace

/-!
# Exact traced checks for the signed outer kernels

The accelerated checker proves the unchanged outer leaf and chain checks.
The original approximation and integral theorems remain responsible for
all analytic conclusions.
-/

namespace ErdosOverlap

open Numerics

public section

structure TracedOuterLeaf where
  leaf : OuterIntegralLeaf
  trace : PolynomialBoxTrace
  deriving Repr

@[expose] def TracedOuterLeaf.upperBox (l : TracedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel) : FixedBox :=
  let m := models l.leaf.cell
  let line := l.trace.range.result.positiveLine
  ((FixedBox.ofRat line.slope).mul (l.trace.integralBox (m.polynomial p) 1 0)).add
    (FixedBox.ofRat (line.constant * (l.leaf.right - l.leaf.left) +
      m.error * (l.leaf.right - l.leaf.left)))

@[expose] def TracedOuterLeaf.check (l : TracedOuterLeaf)
    (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel)
    (caches : ℕ → PolynomialBoxCache) (count : ℕ) : Bool :=
  let m := models l.leaf.cell
  decide (l.leaf.cell < count ∧ 0 < m.radius ∧ l.leaf.left ≤ l.leaf.right ∧
    m.center - m.radius ≤ l.leaf.left ∧ l.leaf.right ≤ m.center + m.radius) &&
    l.trace.check (caches l.leaf.cell) (m.polynomial p) l.leaf.left l.leaf.right &&
    (l.upperBox p models).upperBoundedBy l.leaf.bound

theorem TracedOuterLeaf.upperBox_eq {l : TracedOuterLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache}
    (hc : (caches l.leaf.cell).check ((models l.leaf.cell).polynomial p) = true)
    (ht : l.trace.check (caches l.leaf.cell) ((models l.leaf.cell).polynomial p)
      l.leaf.left l.leaf.right = true) :
    l.upperBox p models = ((models l.leaf.cell).polynomial p).positiveIntegralUpperBox
      l.leaf.left l.leaf.right (models l.leaf.cell).error := by
  simp only [upperBox, PolynomialPiece.positiveIntegralUpperBox,
    l.trace.range_eq ht, PolynomialBoxCache.rangeBox_eq hc,
    l.trace.integralBox_eq ht, PolynomialBoxCache.integralBox_eq hc]

theorem TracedOuterLeaf.check_sound {l : TracedOuterLeaf} {p : OuterFourierPolynomial}
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

@[expose] def outerTracedChainCheck (p : OuterFourierPolynomial)
    (models : ℕ → OuterCellModel) (caches : ℕ → PolynomialBoxCache) (count : ℕ) :
    ℚ → ℚ → List TracedOuterLeaf → Bool
  | a, b, [] => decide (a = b)
  | a, b, l :: ls => decide (l.leaf.left = a) && l.check p models caches count &&
      outerTracedChainCheck p models caches count l.leaf.right b ls

theorem outerChainCheck_of_tracedChain {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {caches : ℕ → PolynomialBoxCache} {count : ℕ}
    (hcache : ∀ j < count, (caches j).check ((models j).polynomial p) = true)
    {a b : ℚ} {leaves : List TracedOuterLeaf}
    (hc : outerTracedChainCheck p models caches count a b leaves = true) :
    outerChainCheck p models count a b (leaves.map TracedOuterLeaf.leaf) = true := by
  induction leaves generalizing a with
  | nil => exact hc
  | cons l ls ih =>
    change (decide (l.leaf.left = a) && l.check p models caches count) &&
      outerTracedChainCheck p models caches count l.leaf.right b ls = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have hh := Bool.and_eq_true_iff.mp hs.1
    change (decide (l.leaf.left = a) && l.leaf.check p models count) &&
      outerChainCheck p models count l.leaf.right b (ls.map TracedOuterLeaf.leaf) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hh.1, l.check_sound hcache hh.2⟩, ih hs.2⟩

end
end ErdosOverlap
