/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Data0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Claim0005 : IntegralClaim := ⟨(16771/32768 : ℚ), (343/512 : ℚ), (Int.ofNat 2565912265383487750603787993088)⟩

theorem profile05Block0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Claim0005 :=
  profileBlock_certificate profile05Leaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
