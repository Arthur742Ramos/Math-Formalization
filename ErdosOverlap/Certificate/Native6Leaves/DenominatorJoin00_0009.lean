/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0018
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0019

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0009Claim : IntegralClaim :=
  ⟨(1145/2048 : ℚ), (62/97 : ℚ), (Int.ofNat 111733570712199870562893971011630268416)⟩

theorem denominatorJoin00_0009 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0009Claim :=
  denominatorBlock0018.glue denominatorBlock0019 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
