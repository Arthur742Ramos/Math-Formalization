/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0006
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0006 : IntegralClaim := ⟨(14623/1048576 : ℚ), (8145/524288 : ℚ), (Int.ofNat 7462271110171585023859060899840)⟩

theorem denominatorBlock0006 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0006 :=
  denominatorBlock_certificate denominatorLeaves0006 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
