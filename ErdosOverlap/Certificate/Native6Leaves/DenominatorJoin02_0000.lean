/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0000
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (4569/262144 : ℚ), (Int.ofNat 50808350934629556673720354865152)⟩

theorem denominatorJoin02_0000 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0000Claim :=
  denominatorJoin01_0000.glue denominatorJoin01_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
