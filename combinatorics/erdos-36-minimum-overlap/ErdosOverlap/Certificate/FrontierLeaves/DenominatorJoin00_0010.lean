/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0020
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0021

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0010Claim : IntegralClaim := ⟨(5349/262144 : ℚ), (2851/131072 : ℚ), 487557182760149981761113329927⟩

theorem denominatorJoin00_0010Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0010Claim :=
  denominatorBlock0020.glue denominatorBlock0021 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
