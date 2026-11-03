module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile13 : filteredProfiles 13 = expectedProfiles.getD 13 [] := by decide
#print axioms profile13
end CoveringProfileChecks
