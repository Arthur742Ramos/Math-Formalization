/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Join00_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join01_0002Claim : IntegralClaim :=
  ⟨(4647/7138 : ℚ), (15859/16384 : ℚ), (Int.ofNat 1453195602546505175930482196480)⟩

theorem profile03Join01_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join01_0002Claim :=
  profile03Join00_0004.glue profile03Join00_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
