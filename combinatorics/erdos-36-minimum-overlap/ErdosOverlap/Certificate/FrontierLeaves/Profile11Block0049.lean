/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Geometry0779
public import ErdosOverlap.Certificate.FrontierLeaves.Geometry0780
public import ErdosOverlap.Certificate.FrontierLeaves.Lambdas
public import ErdosOverlap.Certificate.FrontierLeaves.ProfileTauFacts
public import ErdosOverlap.Numerics.FrontierCheckedLeafLists
public import ErdosOverlap.Numerics.FrontierLeafAssemblyActual
public import ErdosOverlap.Numerics.KernelIntegerSlope
public meta import ErdosOverlap.Numerics.KernelIntegerSlope

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile11Raw0049 : List ProfileLeaf := [
  ⟨g73085, (some 203), (3926108162143/500000000000000000 : ℚ), (-8394506584293673891676206)⟩,
  ⟨g73087, (some 203), (3926108162143/500000000000000000 : ℚ), (-31048699293580153950458392)⟩,
  ⟨g73088, (some 203), (3926108162143/500000000000000000 : ℚ), (-53140510946820042940372503)⟩,
  ⟨g73089, (some 204), (3857641187423/500000000000000000 : ℚ), 0⟩,
  ⟨g73091, (some 204), (3857641187423/500000000000000000 : ℚ), 0⟩,
  ⟨g73092, (some 204), (3857641187423/500000000000000000 : ℚ), 0⟩,
  ⟨g73093, (some 204), (3857641187423/500000000000000000 : ℚ), (-2315588083622315461251288)⟩,
  ⟨g73094, (some 204), (3857641187423/500000000000000000 : ℚ), (-10870123458962058672393507)⟩,
  ⟨g73095, (some 204), (3857641187423/500000000000000000 : ℚ), (-19248939716187756592127897)⟩,
  ⟨g73096, (some 204), (3857641187423/500000000000000000 : ℚ), (-27451331048977752744831236)⟩,
  ⟨g73099, (some 205), (3800967129183/500000000000000000 : ℚ), 0⟩,
  ⟨g73100, (some 205), (3800967129183/500000000000000000 : ℚ), 0⟩,
  ⟨g73102, (some 205), (3800967129183/500000000000000000 : ℚ), 0⟩,
  ⟨g73103, (some 205), (3800967129183/500000000000000000 : ℚ), (-2691094162229259961305577)⟩,
  ⟨g73106, (some 205), (3800967129183/500000000000000000 : ℚ), (-10001344766853261710600132)⟩,
  ⟨g73107, (some 205), (3800967129183/500000000000000000 : ℚ), (-17131821752292945050723988)⟩,
  ⟨g73109, (some 205), (3800967129183/500000000000000000 : ℚ), (-24082120872125867959025477)⟩,
  ⟨g73110, (some 205), (3800967129183/500000000000000000 : ℚ), (-30851882391580889181673495)⟩,
  ⟨g73111, (some 206), (3756358551647/500000000000000000 : ℚ), 0⟩,
  ⟨g73112, (some 206), (3756358551647/500000000000000000 : ℚ), 0⟩,
  ⟨g73113, (some 206), (3756358551647/500000000000000000 : ℚ), (-6154912043327767845590525)⟩,
  ⟨g73114, (some 206), (3756358551647/500000000000000000 : ℚ), (-12199083381782131074497245)⟩,
  ⟨g73116, (some 206), (3756358551647/500000000000000000 : ℚ), (-18061592572419980342032433)⟩,
  ⟨g73117, (some 206), (3756358551647/500000000000000000 : ℚ), (-23742352685978365600772973)⟩,
  ⟨g73119, (some 206), (3756358551647/500000000000000000 : ℚ), (-29241322926674627507160728)⟩,
  ⟨g73120, (some 206), (3756358551647/500000000000000000 : ℚ), (-34558508771401036616115664)⟩
]

noncomputable def profile11Leaves0049 : List (CheckedProfileLeaf ⟨11, by decide⟩) :=
  checkedProfileLeaves ⟨11, by decide⟩ profile11Raw0049 (by erdos_profile_integer_decide mode11TauBase)

noncomputable def profile11Claim0049 : IntegralClaim := ⟨(262087/262144 : ℚ), (1/1 : ℚ), (-361185735459109887102609266)⟩

theorem profile11Block0049 : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Claim0049 :=
  profileBlock_certificate profile11Leaves0049 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
