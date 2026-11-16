/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0004
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0002Claim : IntegralClaim :=
  ⟨(2023/4096 : ℚ), (786649/1040384 : ℚ), (Int.ofNat 325442203945335995594412457557019852800)⟩

theorem denominatorJoin02_0002 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0002Claim :=
  denominatorJoin01_0004.glue denominatorJoin01_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
