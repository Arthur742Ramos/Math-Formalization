/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join01_0001Claim : IntegralClaim :=
  ⟨(61/256 : ℚ), (49177/88064 : ℚ), (Int.ofNat 37035853153538929272282821951488)⟩

theorem profile00Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join01_0001Claim :=
  profile00Join00_0002.glue profile00Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
