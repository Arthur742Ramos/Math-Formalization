/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0012
public import ErdosOverlap.Certificate.Native6Leaves.Profile03Block0013

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile03Join00_0006Claim : IntegralClaim :=
  ⟨(15859/16384 : ℚ), (1/1 : ℚ), (Int.negSucc 5576468607607597275416482545663)⟩

theorem profile03Join00_0006 :
  IntegralClaim.LowerCertificate (profileIntegrand (3 : Fin 10)) (2*approximationError) profile03Join00_0006Claim :=
  profile03Block0012.glue profile03Block0013 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
