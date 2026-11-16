/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0002
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0001Claim : IntegralClaim :=
  ⟨(10653/1048576 : ℚ), (4569/262144 : ℚ), (Int.ofNat 32847702555109634865835005706240)⟩

theorem denominatorJoin01_0001 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0001Claim :=
  denominatorJoin00_0002.glue denominatorJoin00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
