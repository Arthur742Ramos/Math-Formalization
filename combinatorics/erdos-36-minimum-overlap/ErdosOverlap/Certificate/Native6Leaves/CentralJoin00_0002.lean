/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0004
public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0002Claim : IntegralClaim :=
  ⟨(139/512 : ℚ), (43651/65536 : ℚ), (Int.ofNat 34998125029681274075370592665600)⟩

theorem centralJoin00_0002 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0002Claim :=
  centralBlock0004.glue centralBlock0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
