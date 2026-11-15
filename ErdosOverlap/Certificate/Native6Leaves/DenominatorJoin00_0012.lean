/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0024
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0025

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0012Claim : IntegralClaim :=
  ⟨(786649/1040384 : ℚ), (217361/260096 : ℚ), (Int.ofNat 33052426568727126221255960429097648128)⟩

theorem denominatorJoin00_0012 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0012Claim :=
  denominatorBlock0024.glue denominatorBlock0025 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
