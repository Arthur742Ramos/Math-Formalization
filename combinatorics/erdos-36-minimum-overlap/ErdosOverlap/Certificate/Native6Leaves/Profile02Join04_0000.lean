/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join02_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join03_0000

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join04_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (1/1 : ℚ), (Int.ofNat 35895131680889071278010795032576)⟩

theorem profile02Join04_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join04_0000Claim :=
  profile02Join03_0000.glue profile02Join02_0002 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
