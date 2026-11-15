/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin03_0000
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin03_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin04_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (1/1 : ℚ), (Int.ofNat 894002665868146391546233914644620115968)⟩

theorem denominatorJoin04_0000 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin04_0000Claim :=
  denominatorJoin03_0000.glue denominatorJoin03_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
