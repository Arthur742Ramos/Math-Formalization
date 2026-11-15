/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0028
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0029

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0014Claim : IntegralClaim :=
  ⟨(14917/16384 : ℚ), (15959/16384 : ℚ), (Int.ofNat 1962485944142257100295876758242066432)⟩

theorem denominatorJoin00_0014 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0014Claim :=
  denominatorBlock0028.glue denominatorBlock0029 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
