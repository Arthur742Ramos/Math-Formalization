/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile06Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile06Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0003Claim : IntegralClaim :=
  ⟨(86/127 : ℚ), (16297/16384 : ℚ), (Int.negSucc 23639857416598068494327695278079)⟩

theorem profile06Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (6 : Fin 10)) (2*approximationError) profile06Join00_0003Claim :=
  profile06Block0006.glue profile06Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
