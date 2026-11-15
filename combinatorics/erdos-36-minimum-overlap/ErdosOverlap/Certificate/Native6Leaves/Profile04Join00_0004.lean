/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0004Claim : IntegralClaim :=
  ⟨(33765/49664 : ℚ), (15685/16384 : ℚ), (Int.ofNat 293293967285944878390845636608)⟩

theorem profile04Join00_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join00_0004Claim :=
  profile04Block0008.glue profile04Block0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
