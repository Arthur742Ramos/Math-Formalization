/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0023
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0023 : IntegralClaim := ⟨(32525/32768 : ℚ), (1/1 : ℚ), (Int.negSucc 393921834411473562452432519167)⟩

theorem profile02Block0023 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0023 :=
  profileBlock_certificate profile02Leaves0023 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
