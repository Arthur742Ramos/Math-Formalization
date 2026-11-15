/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.OuterDenominators
public import ErdosOverlap.Certificate.CoarseNative6OuterBindings

/-! # Actual physical inequalities for the sixty integrated outer rows

This module's imports require all sixty signed-kernel denominator receipts.
It then inserts their actual cap theorem into the exact source-bin bindings.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

theorem outerRowsNeedingIntegrals_physical :
    PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight :=
  outerRowsNeedingIntegrals_physical_of_positiveBin_cap_bound
    OuterNumerics.positiveBin_cap_bound

theorem outerRows_physical : PhysicalMeanInequalities outerRows auxiliaryHeight :=
  outerRows_physical_of_needed outerRowsNeedingIntegrals_physical

end ErdosOverlap.Certificate.CoarseNative6
