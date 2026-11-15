/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0001Claim : IntegralClaim :=
  ⟨(345/32768 : ℚ), (1327/65536 : ℚ), (Int.negSucc 288230376151711743)⟩

theorem profile01Join00_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0001Claim :=
  profile01Block0002.glue profile01Block0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
