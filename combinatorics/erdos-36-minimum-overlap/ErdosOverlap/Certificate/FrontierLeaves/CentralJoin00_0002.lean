/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0004
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0002Claim : IntegralClaim := ⟨(39/256 : ℚ), (11731/32768 : ℚ), 20220244654847892225241577843605⟩

theorem centralJoin00_0002Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0002Claim :=
  centralBlock0004.glue centralBlock0005 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
