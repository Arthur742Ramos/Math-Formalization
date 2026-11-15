/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0010
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join00_0005Claim : IntegralClaim :=
  ⟨(286441/364544 : ℚ), (15859/16384 : ℚ), (Int.negSucc 288230376151711743)⟩

theorem profile03Join00_0005 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join00_0005Claim :=
  profile03Block0010.glue profile03Block0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
