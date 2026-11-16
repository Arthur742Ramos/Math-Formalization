/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0007
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0007 : IntegralClaim := ⟨(98535/182272 : ℚ), (4647/7138 : ℚ), (Int.ofNat 1773397611410561176089464406016)⟩

theorem profile03Block0007 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0007 :=
  profileBlock_certificate profile03Leaves0007 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
