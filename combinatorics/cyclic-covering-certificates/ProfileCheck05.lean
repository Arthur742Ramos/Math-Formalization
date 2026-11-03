module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile05 : filteredProfiles 5 = expectedProfiles.getD 5 [] := by decide
#print axioms profile05
end CoveringProfileChecks
