/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0024
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0012Claim : IntegralClaim := ⟨(29737/32768 : ℚ), (7955/8192 : ℚ), 0⟩

theorem centralJoin00_0012Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0012Claim :=
  centralBlock0024.glue centralBlock0025 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
