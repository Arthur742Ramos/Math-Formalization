module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile07 : filteredProfiles 7 = expectedProfiles.getD 7 [] := by decide
#print axioms profile07
end CoveringProfileChecks
