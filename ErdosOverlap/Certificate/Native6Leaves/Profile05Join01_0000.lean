/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile05Join00_0000
public import ErdosOverlap.Certificate.Native6Leaves.Profile05Join00_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join01_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (71/256 : ℚ), (Int.negSucc 263795555602224191560797388799)⟩

theorem profile05Join01_0000 :
  IntegralClaim.LowerCertificate (profileIntegrand (5 : Fin 10)) (2*approximationError) profile05Join01_0000Claim :=
  profile05Join00_0000.glue profile05Join00_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
