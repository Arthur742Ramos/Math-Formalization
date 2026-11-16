/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Join00_0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join01_0005Claim : IntegralClaim :=
  ⟨(239/256 : ℚ), (1/1 : ℚ), (Int.negSucc 3952941401981639155899741241343)⟩

theorem profile02Join01_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join01_0005Claim :=
  profile02Join00_0010.glue profile02Join00_0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
