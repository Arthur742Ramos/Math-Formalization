/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0008
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join00_0004Claim : IntegralClaim :=
  ⟨(4647/7138 : ℚ), (286441/364544 : ℚ), (Int.ofNat 1453195602546793406306633908224)⟩

theorem profile03Join00_0004 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join00_0004Claim :=
  profile03Block0008.glue profile03Block0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
