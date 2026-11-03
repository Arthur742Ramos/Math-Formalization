module
public import ProfileData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CoveringProfileChecks
open CoveringProfileData

theorem profile02 : filteredProfiles 2 = expectedProfiles.getD 2 [] := by decide
#print axioms profile02
end CoveringProfileChecks
