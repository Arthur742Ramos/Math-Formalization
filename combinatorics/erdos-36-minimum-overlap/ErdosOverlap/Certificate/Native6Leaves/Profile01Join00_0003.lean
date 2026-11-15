/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0003Claim : IntegralClaim :=
  ⟨(293/1024 : ℚ), (3279/8192 : ℚ), (Int.ofNat 21889777229556807809929077325824)⟩

theorem profile01Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0003Claim :=
  profile01Block0006.glue profile01Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
