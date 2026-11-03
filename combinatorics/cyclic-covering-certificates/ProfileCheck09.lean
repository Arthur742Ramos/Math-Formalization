module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile09 : filteredProfiles 9 = expectedProfiles.getD 9 [] := by decide
#print axioms profile09
end CoveringProfileChecks
