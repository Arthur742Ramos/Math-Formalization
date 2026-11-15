/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join01_0001Claim : IntegralClaim :=
  ⟨(53359/198656 : ℚ), (4647/7138 : ℚ), (Int.ofNat 38340125524972073160591095627776)⟩

theorem profile03Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join01_0001Claim :=
  profile03Join00_0002.glue profile03Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
