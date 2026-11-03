module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile03 : filteredProfiles 3 = expectedProfiles.getD 3 [] := by decide
#print axioms profile03
end CoveringProfileChecks
