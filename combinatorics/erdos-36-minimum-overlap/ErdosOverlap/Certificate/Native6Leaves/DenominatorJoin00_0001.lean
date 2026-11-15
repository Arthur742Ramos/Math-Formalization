/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0002
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0001Claim : IntegralClaim :=
  ⟨(13341/2097152 : ℚ), (10653/1048576 : ℚ), (Int.ofNat 11173684668805392551618572976128)⟩

theorem denominatorJoin00_0001 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0001Claim :=
  denominatorBlock0002.glue denominatorBlock0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
