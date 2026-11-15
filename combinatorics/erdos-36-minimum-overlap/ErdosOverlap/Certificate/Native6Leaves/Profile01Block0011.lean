/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Data0011
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Claim0011 : IntegralClaim := ⟨(180119/339968 : ℚ), (2377/4096 : ℚ), (Int.ofNat 885567779510512856334503772160)⟩

theorem profile01Block0011 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Claim0011 :=
  profileBlock_certificate profile01Leaves0011 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
