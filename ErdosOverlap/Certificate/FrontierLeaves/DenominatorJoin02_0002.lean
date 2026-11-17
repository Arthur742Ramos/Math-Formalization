/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0004
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin02_0002Claim : IntegralClaim := ⟨(64435/4194304 : ℚ), (51257/2097152 : ℚ), 12751187737233957208582869859349⟩

theorem denominatorJoin02_0002Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0002Claim :=
  denominatorJoin01_0004Bound.glue denominatorJoin01_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
