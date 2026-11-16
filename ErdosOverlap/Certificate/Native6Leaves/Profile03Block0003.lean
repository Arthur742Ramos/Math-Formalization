/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0003
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0003 : IntegralClaim := ⟨(1683/65536 : ℚ), (53359/198656 : ℚ), (Int.ofNat 8559279545797467095791828992)⟩

theorem profile03Block0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0003 :=
  profileBlock_certificate profile03Leaves0003 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
