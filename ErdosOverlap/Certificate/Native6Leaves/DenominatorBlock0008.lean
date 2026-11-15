/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0008
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0008 : IntegralClaim := ⟨(4569/262144 : ℚ), (707/32768 : ℚ), (Int.ofNat 10798812563347343440802687746048)⟩

theorem denominatorBlock0008 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0008 :=
  denominatorBlock_certificate denominatorLeaves0008 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
