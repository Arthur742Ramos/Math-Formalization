/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join00_0003Claim : IntegralClaim :=
  ⟨(441389/1040384 : ℚ), (49177/88064 : ℚ), (Int.ofNat 8594481468801543988903092944896)⟩

theorem profile00Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join00_0003Claim :=
  profile00Block0006.glue profile00Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
