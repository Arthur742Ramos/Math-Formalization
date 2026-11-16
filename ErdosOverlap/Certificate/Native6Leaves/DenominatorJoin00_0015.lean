/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0030
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0031

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0015Claim : IntegralClaim :=
  ⟨(15959/16384 : ℚ), (1/1 : ℚ), (Int.ofNat 53837528447286072740404440030248960)⟩

theorem denominatorJoin00_0015 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0015Claim :=
  denominatorBlock0030.glue denominatorBlock0031 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
