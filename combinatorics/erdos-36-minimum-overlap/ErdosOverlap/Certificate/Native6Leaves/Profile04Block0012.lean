/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Data0012
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Claim0012 : IntegralClaim := ⟨(4095/4096 : ℚ), (1/1 : ℚ), (Int.negSucc 19382331721332828849483808767)⟩

theorem profile04Block0012 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Claim0012 :=
  profileBlock_certificate profile04Leaves0012 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
