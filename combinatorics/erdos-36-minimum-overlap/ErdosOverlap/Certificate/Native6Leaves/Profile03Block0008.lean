/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0008
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0008 : IntegralClaim := ⟨(4647/7138 : ℚ), (2813/4096 : ℚ), (Int.ofNat 1206085977543940160463810068480)⟩

theorem profile03Block0008 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0008 :=
  profileBlock_certificate profile03Leaves0008 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
