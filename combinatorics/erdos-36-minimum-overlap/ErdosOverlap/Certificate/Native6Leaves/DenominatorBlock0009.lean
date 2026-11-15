/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0009
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0009 : IntegralClaim := ⟨(707/32768 : ℚ), (3503/131072 : ℚ), (Int.ofNat 32458515442647292676833907048448)⟩

theorem denominatorBlock0009 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0009 :=
  denominatorBlock_certificate denominatorLeaves0009 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
