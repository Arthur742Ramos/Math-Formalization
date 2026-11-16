/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0028
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0029

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0014Claim : IntegralClaim := ⟨(3502137/4194304 : ℚ), (1868035/2097152 : ℚ), 10044050471627038008701446118883353071⟩

theorem denominatorJoin01_0014Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0014Claim :=
  denominatorJoin00_0028Bound.glue denominatorJoin00_0029Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
