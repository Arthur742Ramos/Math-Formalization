/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0012
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0013

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0006Claim : IntegralClaim :=
  ⟨(786649/1040384 : ℚ), (14917/16384 : ℚ), (Int.ofNat 44649885597216279053576238335675858944)⟩

theorem denominatorJoin01_0006 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0006Claim :=
  denominatorJoin00_0012.glue denominatorJoin00_0013 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
