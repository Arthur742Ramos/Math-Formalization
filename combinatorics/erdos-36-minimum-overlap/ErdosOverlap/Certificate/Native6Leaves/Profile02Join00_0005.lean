/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0005Claim : IntegralClaim :=
  ⟨(16377/32768 : ℚ), (2377/4096 : ℚ), (Int.ofNat 3177158576972478896855066869760)⟩

theorem profile02Join00_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0005Claim :=
  profile02Block0010.glue profile02Block0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
