/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0003
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0003 : IntegralClaim := ⟨(527/65536 : ℚ), (10653/1048576 : ℚ), (Int.ofNat 6937013125818004505633719582720)⟩

theorem denominatorBlock0003 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0003 :=
  denominatorBlock_certificate denominatorLeaves0003 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
