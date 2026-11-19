/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0008
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0004Claim : IntegralClaim := ⟨(106311/241664 : ℚ), (1058357/2097152 : ℚ), 4625738277774720504188783171477⟩

theorem centralJoin00_0004Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0004Claim :=
  centralBlock0008.glue centralBlock0009 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
