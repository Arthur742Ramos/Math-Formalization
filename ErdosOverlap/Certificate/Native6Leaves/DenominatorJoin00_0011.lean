/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0022
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0023

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0011Claim : IntegralClaim :=
  ⟨(22417/32768 : ℚ), (786649/1040384 : ℚ), (Int.ofNat 55426681604844533235452820405218181120)⟩

theorem denominatorJoin00_0011 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0011Claim :=
  denominatorBlock0022.glue denominatorBlock0023 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
