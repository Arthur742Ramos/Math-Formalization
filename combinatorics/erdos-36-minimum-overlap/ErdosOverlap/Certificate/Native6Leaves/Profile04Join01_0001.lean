/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join01_0001Claim : IntegralClaim :=
  ⟨(1422/5251 : ℚ), (33765/49664 : ℚ), (Int.ofNat 39386701303414778871004815949824)⟩

theorem profile04Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join01_0001Claim :=
  profile04Join00_0002.glue profile04Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
