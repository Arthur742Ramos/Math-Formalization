/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0008
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0008 : IntegralClaim := ⟨(3279/8192 : ℚ), (1839/4096 : ℚ), (Int.ofNat 3571956762347037157471461310464)⟩

theorem profile02Block0008 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0008 :=
  profileBlock_certificate profile02Leaves0008 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
