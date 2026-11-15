/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile05Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0002Claim : IntegralClaim :=
  ⟨(71/256 : ℚ), (343/512 : ℚ), (Int.ofNat 32351200880560958796562090164224)⟩

theorem profile05Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Join00_0002Claim :=
  profile05Block0004.glue profile05Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
