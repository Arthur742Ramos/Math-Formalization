module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile11 : filteredProfiles 11 = expectedProfiles.getD 11 [] := by decide
#print axioms profile11
end CoveringProfileChecks
