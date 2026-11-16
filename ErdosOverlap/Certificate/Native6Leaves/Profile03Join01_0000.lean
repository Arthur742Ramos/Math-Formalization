/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0000
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join01_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (53359/198656 : ℚ), (Int.ofNat 8559279545365121531564261376)⟩

theorem profile03Join01_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join01_0000Claim :=
  profile03Join00_0000.glue profile03Join00_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
