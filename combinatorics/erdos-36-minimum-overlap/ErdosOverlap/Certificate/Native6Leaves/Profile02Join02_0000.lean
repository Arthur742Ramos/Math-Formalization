/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join01_0000
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join01_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join02_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (3279/8192 : ℚ), (Int.ofNat 26141035972526309903680889946112)⟩

theorem profile02Join02_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join02_0000Claim :=
  profile02Join01_0000.glue profile02Join01_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
