/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0016
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0017

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0008Claim : IntegralClaim :=
  ⟨(96261/130048 : ℚ), (73743/88064 : ℚ), (Int.ofNat 18845630266893423280551624704)⟩

theorem profile02Join00_0008 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0008Claim :=
  profile02Block0016.glue profile02Block0017 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
