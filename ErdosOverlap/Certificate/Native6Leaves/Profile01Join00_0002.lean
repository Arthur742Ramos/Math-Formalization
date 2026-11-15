/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0002Claim : IntegralClaim :=
  ⟨(1327/65536 : ℚ), (293/1024 : ℚ), (Int.ofNat 4251258742970078554504116043776)⟩

theorem profile01Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0002Claim :=
  profile01Block0004.glue profile01Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
