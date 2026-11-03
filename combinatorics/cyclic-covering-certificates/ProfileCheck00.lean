module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile00 : filteredProfiles 0 = expectedProfiles.getD 0 [] := by decide
#print axioms profile00
end CoveringProfileChecks
