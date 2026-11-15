/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join00_0004Claim : IntegralClaim :=
  ⟨(49177/88064 : ℚ), (10997/16384 : ℚ), (Int.ofNat 2379789033259380962477199065088)⟩

theorem profile00Join00_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join00_0004Claim :=
  profile00Block0008.glue profile00Block0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
