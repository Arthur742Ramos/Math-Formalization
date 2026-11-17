/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0044
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0022Claim : IntegralClaim := ⟨(42757/65536 : ℚ), (87351/131072 : ℚ), 15327366107486071618177304276414304238⟩

theorem denominatorJoin00_0022Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0022Claim :=
  denominatorBlock0044.glue denominatorBlock0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
