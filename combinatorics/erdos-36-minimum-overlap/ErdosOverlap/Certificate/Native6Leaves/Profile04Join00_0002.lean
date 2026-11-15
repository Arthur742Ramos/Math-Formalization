/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0004
public import ErdosOverlap.Certificate.Native6Leaves.Profile04Block0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0002Claim : IntegralClaim :=
  ⟨(1422/5251 : ℚ), (16537/32768 : ℚ), (Int.ofNat 34218871327409376641837099384832)⟩

theorem profile04Join00_0002 :
  IntegralClaim.LowerCertificate (profileIntegrand (4 : Fin 10)) (2*approximationError) profile04Join00_0002Claim :=
  profile04Block0004.glue profile04Block0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
