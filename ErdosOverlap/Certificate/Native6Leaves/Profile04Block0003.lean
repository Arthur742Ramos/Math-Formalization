/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Data0003
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Claim0003 : IntegralClaim := ⟨(421/16384 : ℚ), (1422/5251 : ℚ), (Int.ofNat 5642740691784220060109766656)⟩

theorem profile04Block0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Claim0003 :=
  profileBlock_certificate profile04Leaves0003 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
