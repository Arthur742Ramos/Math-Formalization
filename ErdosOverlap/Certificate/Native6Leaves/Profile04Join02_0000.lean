/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join01_0000
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join01_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join02_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (33765/49664 : ℚ), (Int.ofNat 39392344044106130745500698148864)⟩

theorem profile04Join02_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join02_0000Claim :=
  profile04Join01_0000.glue profile04Join01_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
