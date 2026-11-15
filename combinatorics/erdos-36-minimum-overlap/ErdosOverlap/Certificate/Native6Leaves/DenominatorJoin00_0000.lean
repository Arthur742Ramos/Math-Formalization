/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0000
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (13341/2097152 : ℚ), (Int.ofNat 6786963710714529256266776182784)⟩

theorem denominatorJoin00_0000 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0000Claim :=
  denominatorBlock0000.glue denominatorBlock0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
