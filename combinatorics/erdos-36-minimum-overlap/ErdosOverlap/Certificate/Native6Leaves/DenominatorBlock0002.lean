/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0002
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0002 : IntegralClaim := ⟨(13341/2097152 : ℚ), (527/65536 : ℚ), (Int.ofNat 4236671542987388045984853393408)⟩

theorem denominatorBlock0002 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0002 :=
  denominatorBlock_certificate denominatorLeaves0002 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
