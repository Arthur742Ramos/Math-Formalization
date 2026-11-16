/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile06Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile06Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join01_0001Claim : IntegralClaim :=
  ⟨(9/32 : ℚ), (16297/16384 : ℚ), (Int.negSucc 8995354687049785443794269765631)⟩

theorem profile06Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (6 : Fin 10)) (2*approximationError) profile06Join01_0001Claim :=
  profile06Join00_0002.glue profile06Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
