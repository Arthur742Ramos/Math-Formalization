module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile15 : filteredProfiles 15 = expectedProfiles.getD 15 [] := by decide
#print axioms profile15
end CoveringProfileChecks
