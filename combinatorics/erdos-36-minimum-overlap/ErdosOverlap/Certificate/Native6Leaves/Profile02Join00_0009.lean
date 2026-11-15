/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0018
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0019

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0009Claim : IntegralClaim :=
  ⟨(73743/88064 : ℚ), (239/256 : ℚ), (Int.negSucc 288230376151711743)⟩

theorem profile02Join00_0009 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0009Claim :=
  profile02Block0018.glue profile02Block0019 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
