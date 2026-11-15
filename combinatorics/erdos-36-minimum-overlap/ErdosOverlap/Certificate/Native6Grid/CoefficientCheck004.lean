module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck004
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0032 :
    completeCoefficientRowCheck factorRow row0032 32 coefficients0032 = true := by
  have hlen : coefficients0032.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0032 oddDots0032
      641 32 0 coefficients0032 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0032_checked oddSum0032_checked hlen hs

theorem coefficientCheck0033 :
    completeCoefficientRowCheck factorRow row0033 33 coefficients0033 = true := by
  have hlen : coefficients0033.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0033 oddDots0033
      641 33 0 coefficients0033 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0033_checked oddSum0033_checked hlen hs

theorem coefficientCheck0034 :
    completeCoefficientRowCheck factorRow row0034 34 coefficients0034 = true := by
  have hlen : coefficients0034.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0034 oddDots0034
      641 34 0 coefficients0034 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0034_checked oddSum0034_checked hlen hs

theorem coefficientCheck0035 :
    completeCoefficientRowCheck factorRow row0035 35 coefficients0035 = true := by
  have hlen : coefficients0035.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0035 oddDots0035
      641 35 0 coefficients0035 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0035_checked oddSum0035_checked hlen hs

theorem coefficientCheck0036 :
    completeCoefficientRowCheck factorRow row0036 36 coefficients0036 = true := by
  have hlen : coefficients0036.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0036 oddDots0036
      641 36 0 coefficients0036 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0036_checked oddSum0036_checked hlen hs

theorem coefficientCheck0037 :
    completeCoefficientRowCheck factorRow row0037 37 coefficients0037 = true := by
  have hlen : coefficients0037.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0037 oddDots0037
      641 37 0 coefficients0037 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0037_checked oddSum0037_checked hlen hs

theorem coefficientCheck0038 :
    completeCoefficientRowCheck factorRow row0038 38 coefficients0038 = true := by
  have hlen : coefficients0038.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0038 oddDots0038
      641 38 0 coefficients0038 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0038_checked oddSum0038_checked hlen hs

theorem coefficientCheck0039 :
    completeCoefficientRowCheck factorRow row0039 39 coefficients0039 = true := by
  have hlen : coefficients0039.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0039 oddDots0039
      641 39 0 coefficients0039 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0039_checked oddSum0039_checked hlen hs


end
end ErdosOverlap.Native6Grid
