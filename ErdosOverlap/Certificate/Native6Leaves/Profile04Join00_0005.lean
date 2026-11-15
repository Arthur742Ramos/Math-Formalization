/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0005Claim : IntegralClaim :=
  ⟨(15685/16384 : ℚ), (4095/4096 : ℚ), (Int.negSucc 8227203290038239079374176387071)⟩

theorem profile04Join00_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join00_0005Claim :=
  profile04Block0010.glue profile04Block0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
