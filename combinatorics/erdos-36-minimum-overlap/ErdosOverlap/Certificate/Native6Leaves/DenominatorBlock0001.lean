/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0001
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0001 : IntegralClaim := ⟨(3821/1048576 : ℚ), (13341/2097152 : ℚ), (Int.ofNat 5186875716541534132730748469248)⟩

theorem denominatorBlock0001 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0001 :=
  denominatorBlock_certificate denominatorLeaves0001 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
