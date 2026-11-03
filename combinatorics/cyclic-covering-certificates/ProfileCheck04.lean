module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile04 : filteredProfiles 4 = expectedProfiles.getD 4 [] := by decide
#print axioms profile04
end CoveringProfileChecks
