/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0014
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0014 : IntegralClaim := ⟨(43561/65536 : ℚ), (344383/499712 : ℚ), (Int.ofNat 912247066226779217439521505280)⟩

theorem profile02Block0014 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0014 :=
  profileBlock_certificate profile02Leaves0014 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
