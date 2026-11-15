/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.TaylorUniform
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem remainder09_bound :
    cosineRemainderSum Native6Trig.chunk09 taylorGridRadius 20 ≤
      (306 / 10000000000000000 : ℚ) := by
  decide +kernel

end
end ErdosOverlap.Native6Grid
