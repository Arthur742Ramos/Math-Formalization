/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0038
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0039

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0019Claim : IntegralClaim := ⟨(2101/4096 : ℚ), (9283/16384 : ℚ), 88088152392819094171824505122997048836⟩

theorem denominatorJoin00_0019Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0019Claim :=
  denominatorBlock0038.glue denominatorBlock0039 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
