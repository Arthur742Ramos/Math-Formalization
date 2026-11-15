/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Data0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Claim0005 : IntegralClaim := ⟨(4623/11392 : ℚ), (16537/32768 : ℚ), (Int.ofNat 8067914071276570880469870051328)⟩

theorem profile04Block0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Claim0005 :=
  profileBlock_certificate profile04Leaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
