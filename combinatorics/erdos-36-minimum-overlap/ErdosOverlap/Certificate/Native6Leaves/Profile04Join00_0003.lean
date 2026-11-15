/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0003Claim : IntegralClaim :=
  ⟨(16537/32768 : ℚ), (33765/49664 : ℚ), (Int.ofNat 5167829976005402229167716564992)⟩

theorem profile04Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join00_0003Claim :=
  profile04Block0006.glue profile04Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
