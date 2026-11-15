/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0022
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0022 : IntegralClaim := ⟨(22417/32768 : ℚ), (68307/94672 : ℚ), (Int.ofNat 32151164133517901907195235416676499456)⟩

theorem denominatorBlock0022 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0022 :=
  denominatorBlock_certificate denominatorLeaves0022 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
