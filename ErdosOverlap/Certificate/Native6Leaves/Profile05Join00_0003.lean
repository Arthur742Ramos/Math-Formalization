/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile05Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0003Claim : IntegralClaim :=
  ⟨(343/512 : ℚ), (16221/16384 : ℚ), (Int.negSucc 15428532770503673890102367485951)⟩

theorem profile05Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Join00_0003Claim :=
  profile05Block0006.glue profile05Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
