/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join01_0001Claim : IntegralClaim :=
  ⟨(1327/65536 : ℚ), (3279/8192 : ℚ), (Int.ofNat 26141035972526886364433193369600)⟩

theorem profile02Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join01_0001Claim :=
  profile02Join00_0002.glue profile02Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
