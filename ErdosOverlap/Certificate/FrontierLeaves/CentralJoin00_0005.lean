/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0010
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0005Claim : IntegralClaim := ⟨(1058357/2097152 : ℚ), (2879/5080 : ℚ), 2964371509682986062915251217137⟩

theorem centralJoin00_0005Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0005Claim :=
  centralBlock0010.glue centralBlock0011 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
