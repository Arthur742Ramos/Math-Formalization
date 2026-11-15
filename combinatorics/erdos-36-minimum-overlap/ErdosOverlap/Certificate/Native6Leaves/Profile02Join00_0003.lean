/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0003Claim : IntegralClaim :=
  ⟨(293/1024 : ℚ), (3279/8192 : ℚ), (Int.ofNat 21889777229556807809929077325824)⟩

theorem profile02Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0003Claim :=
  profile02Block0006.glue profile02Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
