/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0026
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0027

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0013Claim : IntegralClaim :=
  ⟨(217361/260096 : ℚ), (14917/16384 : ℚ), (Int.ofNat 11597459028489152832320277906578210816)⟩

theorem denominatorJoin00_0013 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0013Claim :=
  denominatorBlock0026.glue denominatorBlock0027 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
