module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile16 : filteredProfiles 16 = expectedProfiles.getD 16 [] := by decide
#print axioms profile16
end CoveringProfileChecks
