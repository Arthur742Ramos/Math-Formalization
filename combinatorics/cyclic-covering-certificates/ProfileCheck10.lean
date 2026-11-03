module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile10 : filteredProfiles 10 = expectedProfiles.getD 10 [] := by decide
#print axioms profile10
end CoveringProfileChecks
