/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join01_0002Claim : IntegralClaim :=
  ⟨(3279/8192 : ℚ), (2377/4096 : ℚ), (Int.ofNat 11245762013326840085709750009856)⟩

theorem profile02Join01_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join01_0002Claim :=
  profile02Join00_0004.glue profile02Join00_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
