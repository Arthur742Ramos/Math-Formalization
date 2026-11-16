/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join01_0003Claim : IntegralClaim :=
  ⟨(13443/16384 : ℚ), (1/1 : ℚ), (Int.negSucc 1051952565232027964707189030911)⟩

theorem profile00Join01_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join01_0003Claim :=
  profile00Join00_0006.glue profile00Join00_0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
