/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join01_0002

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join02_0001Claim : IntegralClaim :=
  ⟨(4647/7138 : ℚ), (1/1 : ℚ), (Int.negSucc 4123273005061092099486000349183)⟩

theorem profile03Join02_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join02_0001Claim :=
  profile03Join01_0002.glue profile03Join00_0006 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
