/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0020
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0020 : IntegralClaim := ⟨(62/97 : ℚ), (10869/16384 : ℚ), (Int.ofNat 27518837463641617587107056366179581952)⟩

theorem denominatorBlock0020 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0020 :=
  denominatorBlock_certificate denominatorLeaves0020 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
