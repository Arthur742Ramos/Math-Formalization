/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile08Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile08Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0002Claim : IntegralClaim :=
  ⟨(9/32 : ℚ), (86/127 : ℚ), (Int.ofNat 14644502729548283050533425512448)⟩

theorem profile08Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (8 : Fin 10)) (2*approximationError) profile08Join00_0002Claim :=
  profile08Block0004.glue profile08Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
