/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0013
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0013 : IntegralClaim := ⟨(185/512 : ℚ), (850591/2080768 : ℚ), (Int.ofNat 83425810716621008022805469919203819520)⟩

theorem denominatorBlock0013 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0013 :=
  denominatorBlock_certificate denominatorLeaves0013 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
