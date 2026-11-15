/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Data0009
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Claim0009 : IntegralClaim := ⟨(2631/4096 : ℚ), (10997/16384 : ℚ), (Int.ofNat 1171550212587709683154703876096)⟩

theorem profile00Block0009 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Claim0009 :=
  profileBlock_certificate profile00Leaves0009 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
