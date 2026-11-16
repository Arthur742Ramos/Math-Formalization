/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0026
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0026 : IntegralClaim := ⟨(217361/260096 : ℚ), (7121/8192 : ℚ), (Int.ofNat 6999324821079021433057453188667408384)⟩

theorem denominatorBlock0026 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0026 :=
  denominatorBlock_certificate denominatorLeaves0026 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
