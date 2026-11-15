/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0004
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0004 : IntegralClaim := ⟨(53359/198656 : ℚ), (3059/8192 : ℚ), (Int.ofNat 24455335111327231058578820300800)⟩

theorem profile03Block0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0004 :=
  profileBlock_certificate profile03Leaves0004 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
