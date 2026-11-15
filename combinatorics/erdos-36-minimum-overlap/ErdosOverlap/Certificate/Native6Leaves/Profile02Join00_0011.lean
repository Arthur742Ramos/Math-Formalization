/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0022
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0023

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0011Claim : IntegralClaim :=
  ⟨(64627/65536 : ℚ), (1/1 : ℚ), (Int.negSucc 2980539792661376447120813326335)⟩

theorem profile02Join00_0011 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0011Claim :=
  profile02Block0022.glue profile02Block0023 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
