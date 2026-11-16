/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0014
public import ErdosOverlap.Certificate.Native6Leaves.Profile01Block0015

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Join00_0007Claim : IntegralClaim :=
  ⟨(43561/65536 : ℚ), (96261/130048 : ℚ), (Int.ofNat 1133927542842743813179432763392)⟩

theorem profile01Join00_0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Join00_0007Claim :=
  profile01Block0014.glue profile01Block0015 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
