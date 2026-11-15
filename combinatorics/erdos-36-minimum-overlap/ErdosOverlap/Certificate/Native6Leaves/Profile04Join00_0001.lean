/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0001Claim : IntegralClaim :=
  ⟨(129/8192 : ℚ), (1422/5251 : ℚ), (Int.ofNat 5642740691640104872033910784)⟩

theorem profile04Join00_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join00_0001Claim :=
  profile04Block0002.glue profile04Block0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
