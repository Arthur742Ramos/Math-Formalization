/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile09Block0006
public import ErdosOverlap.Certificate.Native6Leaves.Profile09Block0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0003Claim : IntegralClaim :=
  ⟨(86/127 : ℚ), (16297/16384 : ℚ), (Int.negSucc 54557756077031578494904796446719)⟩

theorem profile09Join00_0003 :
  IntegralClaim.LowerCertificate (profileIntegrand (9 : Fin 10)) (2*approximationError) profile09Join00_0003Claim :=
  profile09Block0006.glue profile09Block0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
