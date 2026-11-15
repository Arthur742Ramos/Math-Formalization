/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0014
public import ErdosOverlap.Certificate.Native6Leaves.Profile00Block0015

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Join00_0007Claim : IntegralClaim :=
  ⟨(3949/4096 : ℚ), (1/1 : ℚ), (Int.negSucc 1051952565231739734331037319167)⟩

theorem profile00Join00_0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Join00_0007Claim :=
  profile00Block0014.glue profile00Block0015 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
