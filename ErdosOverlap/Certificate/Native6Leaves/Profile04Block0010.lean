/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Data0010
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Claim0010 : IntegralClaim := ⟨(15685/16384 : ℚ), (32193/32768 : ℚ), (Int.negSucc 1926739268693899633975671914495)⟩

theorem profile04Block0010 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Claim0010 :=
  profileBlock_certificate profile04Leaves0010 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
