/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile07Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile07Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join00_0002Claim : IntegralClaim :=
  ⟨(9/32 : ℚ), (86/127 : ℚ), (Int.ofNat 14644502729548283050533425512448)⟩

theorem profile07Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (7 : Fin 10)) (2*approximationError) profile07Join00_0002Claim :=
  profile07Block0004.glue profile07Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
