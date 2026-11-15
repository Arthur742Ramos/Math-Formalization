/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0020
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0021

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0010Claim : IntegralClaim :=
  ⟨(239/256 : ℚ), (16179/16384 : ℚ), (Int.negSucc 879653037179920449031743995903)⟩

theorem profile01Join00_0010 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0010Claim :=
  profile01Block0020.glue profile01Block0021 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
