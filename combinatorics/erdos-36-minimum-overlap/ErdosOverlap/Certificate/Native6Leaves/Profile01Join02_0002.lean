/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join01_0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join01_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join02_0002Claim : IntegralClaim :=
  ⟨(96261/130048 : ℚ), (1/1 : ℚ), (Int.negSucc 3092588225605492841882922778623)⟩

theorem profile01Join02_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join02_0002Claim :=
  profile01Join01_0004.glue profile01Join01_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
