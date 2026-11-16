module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck006
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0048 :
    completeCoefficientRowCheck factorRow row0048 48 coefficients0048 = true := by
  have hlen : coefficients0048.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0048 oddDots0048
      641 48 0 coefficients0048 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0048_checked oddSum0048_checked hlen hs

theorem coefficientCheck0049 :
    completeCoefficientRowCheck factorRow row0049 49 coefficients0049 = true := by
  have hlen : coefficients0049.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0049 oddDots0049
      641 49 0 coefficients0049 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0049_checked oddSum0049_checked hlen hs

theorem coefficientCheck0050 :
    completeCoefficientRowCheck factorRow row0050 50 coefficients0050 = true := by
  have hlen : coefficients0050.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0050 oddDots0050
      641 50 0 coefficients0050 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0050_checked oddSum0050_checked hlen hs

theorem coefficientCheck0051 :
    completeCoefficientRowCheck factorRow row0051 51 coefficients0051 = true := by
  have hlen : coefficients0051.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0051 oddDots0051
      641 51 0 coefficients0051 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0051_checked oddSum0051_checked hlen hs

theorem coefficientCheck0052 :
    completeCoefficientRowCheck factorRow row0052 52 coefficients0052 = true := by
  have hlen : coefficients0052.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0052 oddDots0052
      641 52 0 coefficients0052 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0052_checked oddSum0052_checked hlen hs

theorem coefficientCheck0053 :
    completeCoefficientRowCheck factorRow row0053 53 coefficients0053 = true := by
  have hlen : coefficients0053.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0053 oddDots0053
      641 53 0 coefficients0053 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0053_checked oddSum0053_checked hlen hs

theorem coefficientCheck0054 :
    completeCoefficientRowCheck factorRow row0054 54 coefficients0054 = true := by
  have hlen : coefficients0054.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0054 oddDots0054
      641 54 0 coefficients0054 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0054_checked oddSum0054_checked hlen hs

theorem coefficientCheck0055 :
    completeCoefficientRowCheck factorRow row0055 55 coefficients0055 = true := by
  have hlen : coefficients0055.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0055 oddDots0055
      641 55 0 coefficients0055 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0055_checked oddSum0055_checked hlen hs


end
end ErdosOverlap.Native6Grid
