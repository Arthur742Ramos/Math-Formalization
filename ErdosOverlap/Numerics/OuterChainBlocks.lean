/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCell

/-! # Bounded blocks for exact outer integral chains

Each block may be checked separately.  Concatenation preserves the original
chain predicate, so a large replay need not reduce one long Boolean term.
-/

namespace ErdosOverlap
open Numerics
public section

theorem outerChainCheck_append {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {count : ℕ} {a b c : ℚ}
    {xs ys : List OuterIntegralLeaf}
    (hx : outerChainCheck p models count a b xs = true)
    (hy : outerChainCheck p models count b c ys = true) :
    outerChainCheck p models count a c (xs ++ ys) = true := by
  induction xs generalizing a with
  | nil =>
    have he : a = b := of_decide_eq_true hx
    subst a
    exact hy
  | cons x xs ih =>
    change (decide (x.left = a) && x.check p models count) &&
      outerChainCheck p models count x.right b xs = true at hx
    have hh := Bool.and_eq_true_iff.mp hx
    change (decide (x.left = a) && x.check p models count) &&
      outerChainCheck p models count x.right c (xs ++ ys) = true
    exact Bool.and_eq_true_iff.mpr ⟨hh.1, ih hh.2⟩

end
end ErdosOverlap
