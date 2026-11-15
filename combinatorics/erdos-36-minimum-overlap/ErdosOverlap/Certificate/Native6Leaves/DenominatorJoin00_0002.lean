/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0004
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0002Claim : IntegralClaim :=
  ⟨(10653/1048576 : ℚ), (14623/1048576 : ℚ), (Int.ofNat 20637124870978284718826664755200)⟩

theorem denominatorJoin00_0002 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0002Claim :=
  denominatorBlock0004.glue denominatorBlock0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
