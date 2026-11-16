/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0028
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0028 : IntegralClaim := ⟨(14917/16384 : ℚ), (62417/65536 : ℚ), (Int.ofNat 1716712528178290147497172006342754304)⟩

theorem denominatorBlock0028 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0028 :=
  denominatorBlock_certificate denominatorLeaves0028 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
