/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0008
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0009

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0004Claim : IntegralClaim :=
  ⟨(2023/4096 : ℚ), (62/97 : ℚ), (Int.ofNat 221442846199478973558060301733957992448)⟩

theorem denominatorJoin01_0004 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0004Claim :=
  denominatorJoin00_0008.glue denominatorJoin00_0009 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
