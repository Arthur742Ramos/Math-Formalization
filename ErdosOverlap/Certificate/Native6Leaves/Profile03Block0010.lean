/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0010
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0010 : IntegralClaim := ⟨(286441/364544 : ℚ), (457/512 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile03Block0010 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0010 :=
  profileBlock_certificate profile03Leaves0010 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
