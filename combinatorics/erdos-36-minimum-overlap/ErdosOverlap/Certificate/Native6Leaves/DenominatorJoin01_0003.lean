/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0006
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0003Claim : IntegralClaim :=
  ⟨(5073/16384 : ℚ), (2023/4096 : ℚ), (Int.ofNat 321014182784195852592882358452154793984)⟩

theorem denominatorJoin01_0003 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0003Claim :=
  denominatorJoin00_0006.glue denominatorJoin00_0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
