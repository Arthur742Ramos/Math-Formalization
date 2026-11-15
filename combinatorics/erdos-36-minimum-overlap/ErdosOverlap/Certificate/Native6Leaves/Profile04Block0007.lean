/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Data0007
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Claim0007 : IntegralClaim := ⟨(1305/2048 : ℚ), (33765/49664 : ℚ), (Int.ofNat 1329527319724658696505494863872)⟩

theorem profile04Block0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Claim0007 :=
  profileBlock_certificate profile04Leaves0007 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
