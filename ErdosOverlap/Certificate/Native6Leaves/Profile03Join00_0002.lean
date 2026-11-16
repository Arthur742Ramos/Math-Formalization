/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join00_0002Claim : IntegralClaim :=
  ⟨(53359/198656 : ℚ), (3889/8192 : ℚ), (Int.ofNat 31457044899698066893588318388224)⟩

theorem profile03Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join00_0002Claim :=
  profile03Block0004.glue profile03Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
