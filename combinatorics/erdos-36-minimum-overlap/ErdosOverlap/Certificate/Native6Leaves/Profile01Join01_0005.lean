/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Join00_0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join01_0005Claim : IntegralClaim :=
  ⟨(239/256 : ℚ), (1/1 : ℚ), (Int.negSucc 3111433855872098034787322691583)⟩

theorem profile01Join01_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join01_0005Claim :=
  profile01Join00_0010.glue profile01Join00_0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
