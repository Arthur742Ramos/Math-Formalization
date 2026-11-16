/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile08Block0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile08Block0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0001Claim : IntegralClaim :=
  ⟨(129/8192 : ℚ), (9/32 : ℚ), (Int.ofNat 1536671941371212769828404199424)⟩

theorem profile08Join00_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (8 : Fin 10)) (2*approximationError) profile08Join00_0001Claim :=
  profile08Block0002.glue profile08Block0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
