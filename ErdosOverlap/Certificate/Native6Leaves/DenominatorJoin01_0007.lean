/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0014
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0015

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0007Claim : IntegralClaim :=
  ⟨(14917/16384 : ℚ), (1/1 : ℚ), (Int.ofNat 2016323472589543173036281198272315392)⟩

theorem denominatorJoin01_0007 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0007Claim :=
  denominatorJoin00_0014.glue denominatorJoin00_0015 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
