/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0016
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0017

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0008Claim : IntegralClaim :=
  ⟨(2023/4096 : ℚ), (1145/2048 : ℚ), (Int.ofNat 109709275487279102995166330722327724032)⟩

theorem denominatorJoin00_0008 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0008Claim :=
  denominatorBlock0016.glue denominatorBlock0017 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
