/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile15Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (260211/262144 : ℚ), 991537867656016462431533836604⟩

theorem profile15Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join03_0002Claim :=
  profile15Join02_0004Bound.glue profile15Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
