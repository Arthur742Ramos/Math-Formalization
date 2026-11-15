/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join01_0004Claim : IntegralClaim :=
  ⟨(96261/130048 : ℚ), (239/256 : ℚ), (Int.ofNat 18845630266605192904399912960)⟩

theorem profile01Join01_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join01_0004Claim :=
  profile01Join00_0008.glue profile01Join00_0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
