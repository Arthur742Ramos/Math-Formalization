module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck000
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck001
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck002
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck003
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck004
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck005
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck006
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck007
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck008
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck009
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck010
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck011
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck012
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck013
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck014
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck015
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck016
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck017
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck018
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck019
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck020
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck021
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck022
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck023
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck024
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck025
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck026
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck027
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck028
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck029
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck030
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck031
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck032
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck033
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck034
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck035
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck036
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck037
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck038
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck039
public import ErdosOverlap.Certificate.Native6Grid.SeedCheck040

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem rotationSeedsCheck_append {xs ys : List (CosineTerm × RotationSeed)}
    (hx : rotationSeedsCheck xs = true) (hy : rotationSeedsCheck ys = true) :
    rotationSeedsCheck (xs ++ ys) = true := by
  simpa only [rotationSeedsCheck, List.all_append, hx, hy, Bool.and_self] using
    congrArg₂ Bool.and hx hy

theorem seeds00_checked : rotationSeedsCheck seeds00 = true := by
  change rotationSeedsCheck ((seeds00.take 16) ++ ((seeds00.drop 16).take 16) ++ ((seeds00.drop 32).take 16) ++ ((seeds00.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck000) seedCheck001) seedCheck002) seedCheck003

theorem seeds01_checked : rotationSeedsCheck seeds01 = true := by
  change rotationSeedsCheck ((seeds01.take 16) ++ ((seeds01.drop 16).take 16) ++ ((seeds01.drop 32).take 16) ++ ((seeds01.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck004) seedCheck005) seedCheck006) seedCheck007

theorem seeds02_checked : rotationSeedsCheck seeds02 = true := by
  change rotationSeedsCheck ((seeds02.take 16) ++ ((seeds02.drop 16).take 16) ++ ((seeds02.drop 32).take 16) ++ ((seeds02.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck008) seedCheck009) seedCheck010) seedCheck011

theorem seeds03_checked : rotationSeedsCheck seeds03 = true := by
  change rotationSeedsCheck ((seeds03.take 16) ++ ((seeds03.drop 16).take 16) ++ ((seeds03.drop 32).take 16) ++ ((seeds03.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck012) seedCheck013) seedCheck014) seedCheck015

theorem seeds04_checked : rotationSeedsCheck seeds04 = true := by
  change rotationSeedsCheck ((seeds04.take 16) ++ ((seeds04.drop 16).take 16) ++ ((seeds04.drop 32).take 16) ++ ((seeds04.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck016) seedCheck017) seedCheck018) seedCheck019

theorem seeds05_checked : rotationSeedsCheck seeds05 = true := by
  change rotationSeedsCheck ((seeds05.take 16) ++ ((seeds05.drop 16).take 16) ++ ((seeds05.drop 32).take 16) ++ ((seeds05.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck020) seedCheck021) seedCheck022) seedCheck023

theorem seeds06_checked : rotationSeedsCheck seeds06 = true := by
  change rotationSeedsCheck ((seeds06.take 16) ++ ((seeds06.drop 16).take 16) ++ ((seeds06.drop 32).take 16) ++ ((seeds06.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck024) seedCheck025) seedCheck026) seedCheck027

theorem seeds07_checked : rotationSeedsCheck seeds07 = true := by
  change rotationSeedsCheck ((seeds07.take 16) ++ ((seeds07.drop 16).take 16) ++ ((seeds07.drop 32).take 16) ++ ((seeds07.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck028) seedCheck029) seedCheck030) seedCheck031

theorem seeds08_checked : rotationSeedsCheck seeds08 = true := by
  change rotationSeedsCheck ((seeds08.take 16) ++ ((seeds08.drop 16).take 16) ++ ((seeds08.drop 32).take 16) ++ ((seeds08.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck032) seedCheck033) seedCheck034) seedCheck035

theorem seeds09_checked : rotationSeedsCheck seeds09 = true := by
  change rotationSeedsCheck ((seeds09.take 16) ++ ((seeds09.drop 16).take 16) ++ ((seeds09.drop 32).take 16) ++ ((seeds09.drop 48).take 16)) = true
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seedCheck036) seedCheck037) seedCheck038) seedCheck039

theorem seeds10_checked : rotationSeedsCheck seeds10 = true := by
  change rotationSeedsCheck ((seeds10.take 16)) = true
  exact seedCheck040

theorem seeds_checked : rotationSeedsCheck seeds = true := by
  unfold seeds
  exact rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (rotationSeedsCheck_append (seeds00_checked) seeds01_checked) seeds02_checked) seeds03_checked) seeds04_checked) seeds05_checked) seeds06_checked) seeds07_checked) seeds08_checked) seeds09_checked) seeds10_checked

end
end ErdosOverlap.Native6Grid
