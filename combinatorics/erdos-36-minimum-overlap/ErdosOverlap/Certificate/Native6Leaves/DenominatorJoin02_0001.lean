/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0002
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0001Claim : IntegralClaim :=
  ⟨(4569/262144 : ℚ), (2023/4096 : ℚ), (Int.ofNat 521894202044653639095652263833297223680)⟩

theorem denominatorJoin02_0001 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0001Claim :=
  denominatorJoin01_0002.glue denominatorJoin01_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
