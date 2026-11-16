/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join00_0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join00_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join01_0002Claim : IntegralClaim :=
  ⟨(33765/49664 : ℚ), (4095/4096 : ℚ), (Int.negSucc 7933909322752294200983330750463)⟩

theorem profile04Join01_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join01_0002Claim :=
  profile04Join00_0004.glue profile04Join00_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
