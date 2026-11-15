/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0024
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0024 : IntegralClaim := ⟨(786649/1040384 : ℚ), (278563/352256 : ℚ), (Int.ofNat 17625978762681210592521395483147501568)⟩

theorem denominatorBlock0024 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0024 :=
  denominatorBlock_certificate denominatorLeaves0024 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
