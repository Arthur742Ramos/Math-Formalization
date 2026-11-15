/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Data0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Claim0005 : IntegralClaim := ⟨(3059/8192 : ℚ), (3889/8192 : ℚ), (Int.ofNat 7001709788370835835009498087424)⟩

theorem profile03Block0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Claim0005 :=
  profileBlock_certificate profile03Leaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
