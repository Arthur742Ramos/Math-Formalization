/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0004Claim : IntegralClaim :=
  ⟨(3279/8192 : ℚ), (16377/32768 : ℚ), (Int.ofNat 8068603436354361188854683140096)⟩

theorem profile02Join00_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0004Claim :=
  profile02Block0008.glue profile02Block0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
