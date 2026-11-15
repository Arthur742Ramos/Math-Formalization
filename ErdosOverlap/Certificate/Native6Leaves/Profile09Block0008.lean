/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile09Data0008
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Claim0008 : IntegralClaim := ⟨(16297/16384 : ℚ), (1/1 : ℚ), (Int.negSucc 492227034168732074697174286335)⟩

theorem profile09Block0008 :
  IntegralClaim.LowerCertificate (profileIntegrand (9 : Fin 10)) (2*approximationError) profile09Claim0008 :=
  profileBlock_certificate profile09Leaves0008 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
