/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralData0005
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralClaim0005 : IntegralClaim := ⟨(1029/2048 : ℚ), (43651/65536 : ℚ), (Int.ofNat 3265453693770870010248169521152)⟩

theorem centralBlock0005 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralClaim0005 :=
  centralBlock_certificate centralLeaves0005 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
