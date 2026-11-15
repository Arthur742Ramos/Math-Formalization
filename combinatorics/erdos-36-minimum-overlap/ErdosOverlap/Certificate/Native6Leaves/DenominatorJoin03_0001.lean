/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin02_0002
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin02_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin03_0001Claim : IntegralClaim :=
  ⟨(2023/4096 : ℚ), (1/1 : ℚ), (Int.ofNat 372108413015141817821024977090968027136)⟩

theorem denominatorJoin03_0001 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0001Claim :=
  denominatorJoin02_0002.glue denominatorJoin02_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
