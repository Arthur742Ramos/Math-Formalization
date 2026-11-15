/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile09Data0007
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Claim0007 : IntegralClaim := ⟨(29/30 : ℚ), (16297/16384 : ℚ), (Int.negSucc 26856893139731395512149236252671)⟩

theorem profile09Block0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (9 : Fin 10)) (2*approximationError) profile09Claim0007 :=
  profileBlock_certificate profile09Leaves0007 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
