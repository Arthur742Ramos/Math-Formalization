/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0014
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0015

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0007Claim : IntegralClaim :=
  ⟨(850591/2080768 : ℚ), (2023/4096 : ℚ), (Int.ofNat 153982728863504124402506181971575570432)⟩

theorem denominatorJoin00_0007 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0007Claim :=
  denominatorBlock0014.glue denominatorBlock0015 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
