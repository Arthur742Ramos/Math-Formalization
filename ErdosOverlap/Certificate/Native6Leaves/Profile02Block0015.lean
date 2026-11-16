/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0015
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0015 : IntegralClaim := ⟨(344383/499712 : ℚ), (96261/130048 : ℚ), (Int.ofNat 221680476615964595739911258112)⟩

theorem profile02Block0015 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0015 :=
  profileBlock_certificate profile02Leaves0015 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
