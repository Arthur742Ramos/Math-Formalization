/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0000
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0000 : IntegralClaim := ⟨(0/1 : ℚ), (3821/1048576 : ℚ), (Int.ofNat 1600087994172995123536027713536)⟩

theorem denominatorBlock0000 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0000 :=
  denominatorBlock_certificate denominatorLeaves0000 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
