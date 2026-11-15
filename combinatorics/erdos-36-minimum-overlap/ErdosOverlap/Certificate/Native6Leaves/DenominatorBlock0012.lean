/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0012
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0012 : IntegralClaim := ⟨(5073/16384 : ℚ), (185/512 : ℚ), (Int.ofNat 83605643204070720167570706561375404032)⟩

theorem denominatorBlock0012 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0012 :=
  denominatorBlock_certificate denominatorLeaves0012 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
