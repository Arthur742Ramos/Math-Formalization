/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0017
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0017 : IntegralClaim := ⟨(6429/8192 : ℚ), (73743/88064 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile02Block0017 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0017 :=
  profileBlock_certificate profile02Leaves0017 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
