/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0019
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0019 : IntegralClaim := ⟨(475031/794624 : ℚ), (62/97 : ℚ), (Int.ofNat 53952027884871053581583425374028562432)⟩

theorem denominatorBlock0019 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0019 :=
  denominatorBlock_certificate denominatorLeaves0019 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
