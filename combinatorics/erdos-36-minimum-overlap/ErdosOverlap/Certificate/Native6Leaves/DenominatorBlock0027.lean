/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0027
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0027 : IntegralClaim := ⟨(7121/8192 : ℚ), (14917/16384 : ℚ), (Int.ofNat 4598134207410131399262824717910802432)⟩

theorem denominatorBlock0027 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0027 :=
  denominatorBlock_certificate denominatorLeaves0027 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
