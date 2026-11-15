/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0012
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0013

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join00_0006Claim : IntegralClaim :=
  ⟨(13443/16384 : ℚ), (3949/4096 : ℚ), (Int.negSucc 288230376151711743)⟩

theorem profile00Join00_0006 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join00_0006Claim :=
  profile00Block0012.glue profile00Block0013 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
