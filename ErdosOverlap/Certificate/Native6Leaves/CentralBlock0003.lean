/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralData0003
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralClaim0003 : IntegralClaim := ⟨(421/16384 : ℚ), (139/512 : ℚ), (Int.ofNat 57942863480165790026437754880)⟩

theorem centralBlock0003 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralClaim0003 :=
  centralBlock_certificate centralLeaves0003 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
