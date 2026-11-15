/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile09Data0006
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Claim0006 : IntegralClaim := ⟨(86/127 : ℚ), (29/30 : ℚ), (Int.negSucc 27700862937300182982755560194047)⟩

theorem profile09Block0006 :
  IntegralClaim.LowerCertificate (profileIntegrand (9 : Fin 10)) (2*approximationError) profile09Claim0006 :=
  profileBlock_certificate profile09Leaves0006 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
