/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0020
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorBlock0021

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0010Claim : IntegralClaim :=
  ⟨(62/97 : ℚ), (22417/32768 : ℚ), (Int.ofNat 48572676141012488800899335417843679232)⟩

theorem denominatorJoin00_0010 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0010Claim :=
  denominatorBlock0020.glue denominatorBlock0021 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
