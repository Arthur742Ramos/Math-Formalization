/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Data0012
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Claim0012 : IntegralClaim := ⟨(13443/16384 : ℚ), (58407/65024 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem profile00Block0012 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Claim0012 :=
  profileBlock_certificate profile00Leaves0012 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
