/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0012
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0013

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0006Claim : IntegralClaim :=
  ⟨(2377/4096 : ℚ), (43561/65536 : ℚ), (Int.ofNat 1308501923908211438436063641600)⟩

theorem profile02Join00_0006 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0006Claim :=
  profile02Block0012.glue profile02Block0013 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
