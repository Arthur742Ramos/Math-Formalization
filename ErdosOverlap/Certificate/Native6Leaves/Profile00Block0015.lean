/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile00Data0015
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile00Claim0015 : IntegralClaim := ⟨(32459/32768 : ℚ), (1/1 : ℚ), (Int.negSucc 847929692914371551220125925375)⟩

theorem profile00Block0015 :
  IntegralClaim.LowerCertificate (profileIntegrand (0 : Fin 10)) (2*approximationError) profile00Claim0015 :=
  profileBlock_certificate profile00Leaves0015 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
