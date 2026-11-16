/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile01Data0012
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile01Claim0012 : IntegralClaim := ⟨(2377/4096 : ℚ), (38891/61440 : ℚ), (Int.ofNat 794409781968876758788642701312)⟩

theorem profile01Block0012 :
  IntegralClaim.LowerCertificate (profileIntegrand (1 : Fin 10)) (2*approximationError) profile01Claim0012 :=
  profileBlock_certificate profile01Leaves0012 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
