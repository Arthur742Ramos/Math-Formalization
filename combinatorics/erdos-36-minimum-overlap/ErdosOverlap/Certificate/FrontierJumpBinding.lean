/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierMerge07_000

namespace ErdosOverlap.FrontierJumps
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def finalJumps : List AffineJump := merge07_000

theorem finalJumps_source (t : ℝ) : affineJumpSum finalJumps t =
    affineJumpSum (periodicRowsJumps Native6Data.cells FrontierData.periodicRows) t +
      affineJumpSum (phaseRowsJumps FrontierData.phaseRows) t := by
  simp only [finalJumps, merge07_000_eq, merge06_000_eq, merge05_001_eq, merge05_000_eq, merge04_003_eq, merge04_002_eq, merge04_001_eq, merge04_000_eq, merge03_007_eq, merge03_006_eq, merge03_005_eq, merge03_004_eq, merge03_003_eq, merge03_002_eq, merge03_001_eq, merge03_000_eq, merge02_015_eq, merge02_014_eq, merge02_013_eq, merge02_012_eq, merge02_011_eq, merge02_010_eq, merge02_009_eq, merge02_008_eq, merge02_007_eq, merge02_006_eq, merge02_005_eq, merge02_004_eq, merge02_003_eq, merge02_002_eq, merge02_001_eq, merge02_000_eq, merge01_031_eq, merge01_030_eq, merge01_029_eq, merge01_028_eq, merge01_027_eq, merge01_026_eq, merge01_025_eq, merge01_024_eq, merge01_023_eq, merge01_022_eq, merge01_021_eq, merge01_020_eq, merge01_019_eq, merge01_018_eq, merge01_017_eq, merge01_016_eq, merge01_015_eq, merge01_014_eq, merge01_013_eq, merge01_012_eq, merge01_011_eq, merge01_010_eq, merge01_009_eq, merge01_008_eq, merge01_007_eq, merge01_006_eq, merge01_005_eq, merge01_004_eq, merge01_003_eq, merge01_002_eq, merge01_001_eq, merge01_000_eq, merge00_064_eq, merge00_063_eq, merge00_062_eq, merge00_061_eq, merge00_060_eq, merge00_059_eq, merge00_058_eq, merge00_057_eq, merge00_056_eq, merge00_055_eq, merge00_054_eq, merge00_053_eq, merge00_052_eq, merge00_051_eq, merge00_050_eq, merge00_049_eq, merge00_048_eq, merge00_047_eq, merge00_046_eq, merge00_045_eq, merge00_044_eq, merge00_043_eq, merge00_042_eq, merge00_041_eq, merge00_040_eq, merge00_039_eq, merge00_038_eq, merge00_037_eq, merge00_036_eq, merge00_035_eq, merge00_034_eq, merge00_033_eq, merge00_032_eq, merge00_031_eq, merge00_030_eq, merge00_029_eq, merge00_028_eq, merge00_027_eq, merge00_026_eq, merge00_025_eq, merge00_024_eq, merge00_023_eq, merge00_022_eq, merge00_021_eq, merge00_020_eq, merge00_019_eq, merge00_018_eq, merge00_017_eq, merge00_016_eq, merge00_015_eq, merge00_014_eq, merge00_013_eq, merge00_012_eq, merge00_011_eq, merge00_010_eq, merge00_009_eq, merge00_008_eq, merge00_007_eq, merge00_006_eq, merge00_005_eq, merge00_004_eq, merge00_003_eq, merge00_002_eq, merge00_001_eq, merge00_000_eq, affineJumpSum_mergeCompressed]
  simp only [periodic000_value, periodic001_value, periodic002_value, periodic003_value, periodic004_value, periodic005_value, periodic006_value, periodic007_value, periodic008_value, periodic009_value, periodic010_value, periodic011_value, periodic012_value, periodic013_value, periodic014_value, periodic015_value, periodic016_value, periodic017_value, periodic018_value, periodic019_value, periodic020_value, periodic021_value, periodic022_value, periodic023_value, periodic024_value, periodic025_value, periodic026_value, periodic027_value, periodic028_value, periodic029_value, periodic030_value, periodic031_value, periodic032_value, periodic033_value, periodic034_value, periodic035_value, periodic036_value, periodic037_value, periodic038_value, periodic039_value, periodic040_value, periodic041_value, periodic042_value, periodic043_value, periodic044_value, periodic045_value, periodic046_value, periodic047_value, periodic048_value, periodic049_value, periodic050_value, periodic051_value, periodic052_value, periodic053_value, periodic054_value, periodic055_value, periodic056_value, periodic057_value, periodic058_value, periodic059_value, periodic060_value, periodic061_value, periodic062_value, periodic063_value, periodic064_value, periodic065_value, periodic066_value, periodic067_value, periodic068_value, periodic069_value, periodic070_value, periodic071_value, periodic072_value, periodic073_value, periodic074_value, periodic075_value, periodic076_value, periodic077_value, periodic078_value, periodic079_value, periodic080_value, periodic081_value, periodic082_value, periodic083_value, periodic084_value, periodic085_value, periodic086_value, periodic087_value, periodic088_value, periodic089_value, periodic090_value, periodic091_value, periodic092_value, periodic093_value, periodic094_value, periodic095_value, periodic096_value, periodic097_value, periodic098_value, periodic099_value, periodic100_value, periodic101_value, periodic102_value, periodic103_value, periodic104_value, periodic105_value, periodic106_value, phase00_eq, phase01_eq, phase02_eq, phase03_eq, phase04_eq, phase05_eq, phase06_eq, phase07_eq, phase08_eq, phase09_eq, phase10_eq, phase11_eq, phase12_eq, phase13_eq, phase14_eq, phase15_eq, phase16_eq, phase17_eq, phase18_eq, phase19_eq, phase20_eq, phase21_eq, phase22_eq, affineJumpSum_compressed]
  have hempty : affineJumpSum [] t = 0 := rfl
  simp only [FrontierData.periodicRows, FrontierData.phaseRows, Native6Data.cells,
    periodicRowsJumps_append, phaseRowsJumps, affineJumpSum_append,
    hempty, add_zero, add_assoc]

theorem finalJumps_isChain : finalJumps.IsChain (fun a b => a.knot ≤ b.knot) := by
  decide +kernel

theorem finalJumps_sorted : finalJumps.Pairwise (fun a b => a.knot ≤ b.knot) := by
  letI : Trans (fun a b : AffineJump => a.knot ≤ b.knot)
      (fun a b : AffineJump => a.knot ≤ b.knot) (fun a b : AffineJump => a.knot ≤ b.knot) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  exact finalJumps_isChain.pairwise

end
end ErdosOverlap.FrontierJumps
