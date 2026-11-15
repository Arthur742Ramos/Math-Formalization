/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join00_0005Claim : IntegralClaim :=
  ⟨(10997/16384 : ℚ), (13443/16384 : ℚ), (Int.ofNat 418511892761682282941882826752)⟩

theorem profile00Join00_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join00_0005Claim :=
  profile00Block0010.glue profile00Block0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
