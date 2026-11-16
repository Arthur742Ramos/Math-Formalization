/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin02_0000
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin02_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin03_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (2023/4096 : ℚ), (Int.ofNat 521894252853004573725208937553652088832)⟩

theorem denominatorJoin03_0000 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0000Claim :=
  denominatorJoin02_0000.glue denominatorJoin02_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
