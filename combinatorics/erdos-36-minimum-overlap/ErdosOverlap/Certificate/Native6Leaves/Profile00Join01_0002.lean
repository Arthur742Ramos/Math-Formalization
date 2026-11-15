/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Join00_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join01_0002Claim : IntegralClaim :=
  ⟨(49177/88064 : ℚ), (13443/16384 : ℚ), (Int.ofNat 2798300926021063245419081891840)⟩

theorem profile00Join01_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join01_0002Claim :=
  profile00Join00_0004.glue profile00Join00_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
