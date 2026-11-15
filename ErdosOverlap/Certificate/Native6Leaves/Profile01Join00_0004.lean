/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0004Claim : IntegralClaim :=
  ⟨(3279/8192 : ℚ), (16377/32768 : ℚ), (Int.ofNat 8068603436354361188854683140096)⟩

theorem profile01Join00_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0004Claim :=
  profile01Block0008.glue profile01Block0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
