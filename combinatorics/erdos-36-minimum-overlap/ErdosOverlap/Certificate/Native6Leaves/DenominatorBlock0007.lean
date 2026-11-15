/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0007
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0007 : IntegralClaim := ⟨(8145/524288 : ℚ), (4569/262144 : ℚ), (Int.ofNat 4748306573959765123149280051200)⟩

theorem denominatorBlock0007 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0007 :=
  denominatorBlock_certificate denominatorLeaves0007 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
