/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0015
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0015 : IntegralClaim := ⟨(1049273/2326528 : ℚ), (2023/4096 : ℚ), (Int.ofNat 77281402122745432388854273925888081920)⟩

theorem denominatorBlock0015 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0015 :=
  denominatorBlock_certificate denominatorLeaves0015 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
