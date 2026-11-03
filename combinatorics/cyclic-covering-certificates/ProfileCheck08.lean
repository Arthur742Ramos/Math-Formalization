module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile08 : filteredProfiles 8 = expectedProfiles.getD 8 [] := by decide
#print axioms profile08
end CoveringProfileChecks
