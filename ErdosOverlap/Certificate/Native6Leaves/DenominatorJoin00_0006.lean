/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0012
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0013

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0006Claim : IntegralClaim :=
  ⟨(5073/16384 : ℚ), (850591/2080768 : ℚ), (Int.ofNat 167031453920691728190376176480579223552)⟩

theorem denominatorJoin00_0006 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0006Claim :=
  denominatorBlock0012.glue denominatorBlock0013 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
