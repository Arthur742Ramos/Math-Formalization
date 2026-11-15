/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0008
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0004Claim : IntegralClaim :=
  ⟨(4569/262144 : ℚ), (3503/131072 : ℚ), (Int.ofNat 43257328005994636117636594794496)⟩

theorem denominatorJoin00_0004 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0004Claim :=
  denominatorBlock0008.glue denominatorBlock0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
