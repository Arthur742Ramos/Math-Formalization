/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile02Data0022
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile02Claim0022 : IntegralClaim := ⟨(64627/65536 : ℚ), (32525/32768 : ℚ), (Int.negSucc 2586617958249902884668380807167)⟩

theorem profile02Block0022 :
  IntegralClaim.LowerCertificate (profileIntegrand (2 : Fin 10)) (2*approximationError) profile02Claim0022 :=
  profileBlock_certificate profile02Leaves0022 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
