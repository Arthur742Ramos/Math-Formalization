/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0012
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0012 : IntegralClaim := ⟨(15859/16384 : ℚ), (16213/16384 : ℚ), (Int.negSucc 4074861105640125806372399874047)⟩

theorem profile03Block0012 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0012 :=
  profileBlock_certificate profile03Leaves0012 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
