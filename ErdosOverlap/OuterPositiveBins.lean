/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.OuterExpectation

/-! # The sixty positive outer bins requiring numerical integration -/

namespace ErdosOverlap.OuterNumerics
open MeasureTheory Set
@[expose] public section

def positiveBins : List OuterBinData := Outer180.bins09 ++ Outer180.bins10 ++ Outer180.bins11 ++ Outer180.bins12 ++ Outer180.bins13 ++ Outer180.bins14

theorem positiveBins_mem {b : OuterBinData} (hb : b ∈ positiveBins) : b ∈ Outer180.bins := by
  have hm : b ∈ ((Outer180.bins00 ++ Outer180.bins01 ++ Outer180.bins02 ++ Outer180.bins03 ++ Outer180.bins04 ++ Outer180.bins05 ++ Outer180.bins06 ++ Outer180.bins07 ++ Outer180.bins08) ++ positiveBins) ++ (Outer180.bins15 ++ Outer180.bins16 ++ Outer180.bins17) :=
    List.mem_append_left _ (List.mem_append_right _ hb)
  simpa only [Outer180.bins, positiveBins, List.append_assoc] using hm

end
end ErdosOverlap.OuterNumerics
