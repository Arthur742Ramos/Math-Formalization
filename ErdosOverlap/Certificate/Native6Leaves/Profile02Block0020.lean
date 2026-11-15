/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0020
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0020 : IntegralClaim := ⟨(239/256 : ℚ), (31745/32768 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile02Block0020 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0020 :=
  profileBlock_certificate profile02Leaves0020 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
