/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile07Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile07Join02_0000

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join03_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (1/1 : ℚ), (Int.negSucc 12950395597746034654831351693311)⟩

theorem profile07Join03_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (7 : Fin 10)) (2*approximationError) profile07Join03_0000Claim :=
  profile07Join02_0000.glue profile07Block0008 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
