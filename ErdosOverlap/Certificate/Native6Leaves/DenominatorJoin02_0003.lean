/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0006
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin01_0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0003Claim : IntegralClaim :=
  ⟨(786649/1040384 : ℚ), (1/1 : ℚ), (Int.ofNat 46666209069805822226612519533948174336)⟩

theorem denominatorJoin02_0003 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0003Claim :=
  denominatorJoin01_0006.glue denominatorJoin01_0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
