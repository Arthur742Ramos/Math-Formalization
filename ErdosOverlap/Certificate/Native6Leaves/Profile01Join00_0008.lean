/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0016
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0017

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0008Claim : IntegralClaim :=
  ⟨(96261/130048 : ℚ), (73743/88064 : ℚ), (Int.ofNat 18845630266893423280551624704)⟩

theorem profile01Join00_0008 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0008Claim :=
  profile01Block0016.glue profile01Block0017 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
