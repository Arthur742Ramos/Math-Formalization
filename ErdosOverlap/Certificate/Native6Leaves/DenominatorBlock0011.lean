/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0011
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0011 : IntegralClaim := ⟨(12/59 : ℚ), (5073/16384 : ℚ), (Int.ofNat 131419423653312422548767038737441882112)⟩

theorem denominatorBlock0011 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0011 :=
  denominatorBlock_certificate denominatorLeaves0011 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
