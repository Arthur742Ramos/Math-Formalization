/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join01_0003Claim : IntegralClaim :=
  ⟨(2377/4096 : ℚ), (96261/130048 : ℚ), (Int.ofNat 2442429466750955251615496404992)⟩

theorem profile01Join01_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join01_0003Claim :=
  profile01Join00_0006.glue profile01Join00_0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
