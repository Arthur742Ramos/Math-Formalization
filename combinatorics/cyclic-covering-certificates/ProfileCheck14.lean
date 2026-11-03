module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile14 : filteredProfiles 14 = expectedProfiles.getD 14 [] := by decide
#print axioms profile14
end CoveringProfileChecks
