/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Data0018
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Claim0018 : IntegralClaim := ⟨(73743/88064 : ℚ), (112/127 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile01Block0018 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Claim0018 :=
  profileBlock_certificate profile01Leaves0018 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
