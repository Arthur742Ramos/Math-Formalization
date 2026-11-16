/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0010
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0011

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0005Claim : IntegralClaim :=
  ⟨(3503/131072 : ℚ), (5073/16384 : ℚ), (Int.ofNat 200879976003129780508133787744547635200)⟩

theorem denominatorJoin00_0005 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0005Claim :=
  denominatorBlock0010.glue denominatorBlock0011 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
