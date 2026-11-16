/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0014
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0014 : IntegralClaim := ⟨(850591/2080768 : ℚ), (1049273/2326528 : ℚ), (Int.ofNat 76701326740758692013651908045687488512)⟩

theorem denominatorBlock0014 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0014 :=
  denominatorBlock_certificate denominatorLeaves0014 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
