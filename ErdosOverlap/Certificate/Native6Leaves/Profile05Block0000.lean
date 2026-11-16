/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Data0000
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Claim0000 : IntegralClaim := ⟨(0/1 : ℚ), (1/128 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile05Block0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Claim0000 :=
  profileBlock_certificate profile05Leaves0000 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
