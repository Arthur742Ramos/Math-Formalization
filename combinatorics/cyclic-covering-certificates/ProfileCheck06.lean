module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile06 : filteredProfiles 6 = expectedProfiles.getD 6 [] := by decide
#print axioms profile06
end CoveringProfileChecks
