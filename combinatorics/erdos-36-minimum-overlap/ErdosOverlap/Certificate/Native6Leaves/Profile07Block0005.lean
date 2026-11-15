/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile07Data0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Claim0005 : IntegralClaim := ⟨(69/128 : ℚ), (86/127 : ℚ), (Int.ofNat 1670827950817886223303169802240)⟩

theorem profile07Block0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (7 : Fin 10)) (2*approximationError) profile07Claim0005 :=
  profileBlock_certificate profile07Leaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
