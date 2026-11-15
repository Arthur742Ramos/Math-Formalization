/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile06Data0004
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Claim0004 : IntegralClaim := ⟨(9/32 : ℚ), (69/128 : ℚ), (Int.ofNat 12973674778730396827230255710208)⟩

theorem profile06Block0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (6 : Fin 10)) (2*approximationError) profile06Claim0004 :=
  profileBlock_certificate profile06Leaves0004 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
