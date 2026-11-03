module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile01 : filteredProfiles 1 = expectedProfiles.getD 1 [] := by decide
#print axioms profile01
end CoveringProfileChecks
