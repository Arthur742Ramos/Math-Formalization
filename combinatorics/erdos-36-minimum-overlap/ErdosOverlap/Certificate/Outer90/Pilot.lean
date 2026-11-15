/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.OuterApproximation
public import ErdosOverlap.Certificate.Outer90.Seeds00
public import ErdosOverlap.Certificate.OuterData17

/-! # Outer coefficient pilot -/

namespace ErdosOverlap.OuterNumerics
open Numerics
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def pilotCoefficients : List ℚ := [(-221030406621593/140737488355328), (170431699907921/562949953421312), (39258113809545/281474976710656), (-21592913057085/562949953421312), (-1758880448325/562949953421312), (1292428516483/1125899906842624), (34568675113/1125899906842624), (-20932281745/1125899906842624), (-49026943/562949953421312), (53557477/281474976710656), (-619971/562949953421312), (-1500679/1125899906842624), (16305/1125899906842624), (7587/1125899906842624), (-25/281474976710656), (-29/1125899906842624), 0, 0, 0, 0]

theorem pilot_checked : Outer180.polynomial203.approximationCheck seeds00 (1/32) pilotCoefficients (1/100000000000) (1/100000000) = true := by
  decide +kernel

end
end ErdosOverlap.OuterNumerics
