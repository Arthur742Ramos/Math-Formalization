/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join01_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join01_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join02_0001Claim : IntegralClaim :=
  ⟨(49177/88064 : ℚ), (1/1 : ℚ), (Int.ofNat 1746348360789035280711892860928)⟩

theorem profile00Join02_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join02_0001Claim :=
  profile00Join01_0002.glue profile00Join01_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
