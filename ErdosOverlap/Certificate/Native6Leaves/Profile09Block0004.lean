/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile09Data0004
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Claim0004 : IntegralClaim := ⟨(9/32 : ℚ), (69/128 : ℚ), (Int.ofNat 12973674778730396827230255710208)⟩

theorem profile09Block0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (9 : Fin 10)) (2*approximationError) profile09Claim0004 :=
  profileBlock_certificate profile09Leaves0004 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
