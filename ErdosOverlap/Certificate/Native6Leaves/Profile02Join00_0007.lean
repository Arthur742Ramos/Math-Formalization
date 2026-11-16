/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0014
public import ErdosOverlap.Certificate.Native6Leaves.Profile02Block0015

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Join00_0007Claim : IntegralClaim :=
  ⟨(43561/65536 : ℚ), (96261/130048 : ℚ), (Int.ofNat 1133927542842743813179432763392)⟩

theorem profile02Join00_0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Join00_0007Claim :=
  profile02Block0014.glue profile02Block0015 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
