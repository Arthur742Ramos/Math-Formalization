module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile12 : filteredProfiles 12 = expectedProfiles.getD 12 [] := by decide
#print axioms profile12
end CoveringProfileChecks
