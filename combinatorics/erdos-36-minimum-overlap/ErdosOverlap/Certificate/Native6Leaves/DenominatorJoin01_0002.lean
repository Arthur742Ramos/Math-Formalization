/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0004
public import ErdosOverlap.Certificate.Native6Leaves.DenominatorJoin00_0005

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0002Claim : IntegralClaim :=
  ⟨(4569/262144 : ℚ), (5073/16384 : ℚ), (Int.ofNat 200880019260457786502769905381142429696)⟩

theorem denominatorJoin01_0002 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0002Claim :=
  denominatorJoin00_0004.glue denominatorJoin00_0005 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
