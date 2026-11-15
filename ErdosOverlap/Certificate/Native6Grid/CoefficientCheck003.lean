module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck003
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0024 :
    completeCoefficientRowCheck factorRow row0024 24 coefficients0024 = true := by
  have hlen : coefficients0024.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0024 oddDots0024
      641 24 0 coefficients0024 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0024_checked oddSum0024_checked hlen hs

theorem coefficientCheck0025 :
    completeCoefficientRowCheck factorRow row0025 25 coefficients0025 = true := by
  have hlen : coefficients0025.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0025 oddDots0025
      641 25 0 coefficients0025 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0025_checked oddSum0025_checked hlen hs

theorem coefficientCheck0026 :
    completeCoefficientRowCheck factorRow row0026 26 coefficients0026 = true := by
  have hlen : coefficients0026.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0026 oddDots0026
      641 26 0 coefficients0026 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0026_checked oddSum0026_checked hlen hs

theorem coefficientCheck0027 :
    completeCoefficientRowCheck factorRow row0027 27 coefficients0027 = true := by
  have hlen : coefficients0027.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0027 oddDots0027
      641 27 0 coefficients0027 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0027_checked oddSum0027_checked hlen hs

theorem coefficientCheck0028 :
    completeCoefficientRowCheck factorRow row0028 28 coefficients0028 = true := by
  have hlen : coefficients0028.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0028 oddDots0028
      641 28 0 coefficients0028 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0028_checked oddSum0028_checked hlen hs

theorem coefficientCheck0029 :
    completeCoefficientRowCheck factorRow row0029 29 coefficients0029 = true := by
  have hlen : coefficients0029.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0029 oddDots0029
      641 29 0 coefficients0029 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0029_checked oddSum0029_checked hlen hs

theorem coefficientCheck0030 :
    completeCoefficientRowCheck factorRow row0030 30 coefficients0030 = true := by
  have hlen : coefficients0030.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0030 oddDots0030
      641 30 0 coefficients0030 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0030_checked oddSum0030_checked hlen hs

theorem coefficientCheck0031 :
    completeCoefficientRowCheck factorRow row0031 31 coefficients0031 = true := by
  have hlen : coefficients0031.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0031 oddDots0031
      641 31 0 coefficients0031 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0031_checked oddSum0031_checked hlen hs


end
end ErdosOverlap.Native6Grid
