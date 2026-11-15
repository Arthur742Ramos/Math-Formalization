/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0004
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0004 : IntegralClaim := ⟨(10653/1048576 : ℚ), (6343/524288 : ℚ), (Int.ofNat 7725975071143197196138221404160)⟩

theorem denominatorBlock0004 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0004 :=
  denominatorBlock_certificate denominatorLeaves0004 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
