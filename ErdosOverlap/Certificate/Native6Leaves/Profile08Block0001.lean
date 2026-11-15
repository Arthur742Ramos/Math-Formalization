/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile08Data0001
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Claim0001 : IntegralClaim := ⟨(1/128 : ℚ), (129/8192 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile08Block0001 :
  IntegralClaim.LowerCertificate (profileIntegrand (8 : Fin 10)) (2*approximationError) profile08Claim0001 :=
  profileBlock_certificate profile08Leaves0001 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
