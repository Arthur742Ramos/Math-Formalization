/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0022
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0023

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0011Claim : IntegralClaim :=
  ⟨(16179/16384 : ℚ), (1/1 : ℚ), (Int.negSucc 2231780818692177585755578695679)⟩

theorem profile01Join00_0011 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0011Claim :=
  profile01Block0022.glue profile01Block0023 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
