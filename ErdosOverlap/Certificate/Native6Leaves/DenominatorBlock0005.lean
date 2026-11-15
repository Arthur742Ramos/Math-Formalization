/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0005 : IntegralClaim := ⟨(6343/524288 : ℚ), (14623/1048576 : ℚ), (Int.ofNat 12911149799835087522688443351040)⟩

theorem denominatorBlock0005 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0005 :=
  denominatorBlock_certificate denominatorLeaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
