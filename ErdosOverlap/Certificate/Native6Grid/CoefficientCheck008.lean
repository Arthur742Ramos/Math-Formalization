module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck008
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0064 :
    completeCoefficientRowCheck factorRow row0064 64 coefficients0064 = true := by
  have hlen : coefficients0064.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0064 oddDots0064
      641 64 0 coefficients0064 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0064_checked oddSum0064_checked hlen hs

theorem coefficientCheck0065 :
    completeCoefficientRowCheck factorRow row0065 65 coefficients0065 = true := by
  have hlen : coefficients0065.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0065 oddDots0065
      641 65 0 coefficients0065 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0065_checked oddSum0065_checked hlen hs

theorem coefficientCheck0066 :
    completeCoefficientRowCheck factorRow row0066 66 coefficients0066 = true := by
  have hlen : coefficients0066.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0066 oddDots0066
      641 66 0 coefficients0066 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0066_checked oddSum0066_checked hlen hs

theorem coefficientCheck0067 :
    completeCoefficientRowCheck factorRow row0067 67 coefficients0067 = true := by
  have hlen : coefficients0067.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0067 oddDots0067
      641 67 0 coefficients0067 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0067_checked oddSum0067_checked hlen hs

theorem coefficientCheck0068 :
    completeCoefficientRowCheck factorRow row0068 68 coefficients0068 = true := by
  have hlen : coefficients0068.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0068 oddDots0068
      641 68 0 coefficients0068 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0068_checked oddSum0068_checked hlen hs

theorem coefficientCheck0069 :
    completeCoefficientRowCheck factorRow row0069 69 coefficients0069 = true := by
  have hlen : coefficients0069.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0069 oddDots0069
      641 69 0 coefficients0069 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0069_checked oddSum0069_checked hlen hs

theorem coefficientCheck0070 :
    completeCoefficientRowCheck factorRow row0070 70 coefficients0070 = true := by
  have hlen : coefficients0070.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0070 oddDots0070
      641 70 0 coefficients0070 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0070_checked oddSum0070_checked hlen hs

theorem coefficientCheck0071 :
    completeCoefficientRowCheck factorRow row0071 71 coefficients0071 = true := by
  have hlen : coefficients0071.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0071 oddDots0071
      641 71 0 coefficients0071 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0071_checked oddSum0071_checked hlen hs


end
end ErdosOverlap.Native6Grid
