/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Join00_0002
public import ErdosOverlap.Certificate.Native6Leaves.Profile05Join00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join01_0001Claim : IntegralClaim :=
  ⟨(71/256 : ℚ), (16221/16384 : ℚ), (Int.ofNat 16922668110057284906459722678272)⟩

theorem profile05Join01_0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Join01_0001Claim :=
  profile05Join00_0002.glue profile05Join00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
