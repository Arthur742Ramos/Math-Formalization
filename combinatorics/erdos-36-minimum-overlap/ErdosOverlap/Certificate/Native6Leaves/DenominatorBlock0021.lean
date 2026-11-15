/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0021
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0021 : IntegralClaim := ⟨(10869/16384 : ℚ), (22417/32768 : ℚ), (Int.ofNat 21053838677370871213792279051664097280)⟩

theorem denominatorBlock0021 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0021 :=
  denominatorBlock_certificate denominatorLeaves0021 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
