/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0006
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0003Claim : IntegralClaim :=
  ⟨(14623/1048576 : ℚ), (4569/262144 : ℚ), (Int.ofNat 12210577684131350147008340951040)⟩

theorem denominatorJoin00_0003 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0003Claim :=
  denominatorBlock0006.glue denominatorBlock0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
