module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck012
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0096 :
    completeCoefficientRowCheck factorRow row0096 96 coefficients0096 = true := by
  have hlen : coefficients0096.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0096 oddDots0096
      641 96 0 coefficients0096 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0096_checked oddSum0096_checked hlen hs

theorem coefficientCheck0097 :
    completeCoefficientRowCheck factorRow row0097 97 coefficients0097 = true := by
  have hlen : coefficients0097.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0097 oddDots0097
      641 97 0 coefficients0097 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0097_checked oddSum0097_checked hlen hs

theorem coefficientCheck0098 :
    completeCoefficientRowCheck factorRow row0098 98 coefficients0098 = true := by
  have hlen : coefficients0098.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0098 oddDots0098
      641 98 0 coefficients0098 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0098_checked oddSum0098_checked hlen hs

theorem coefficientCheck0099 :
    completeCoefficientRowCheck factorRow row0099 99 coefficients0099 = true := by
  have hlen : coefficients0099.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0099 oddDots0099
      641 99 0 coefficients0099 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0099_checked oddSum0099_checked hlen hs

theorem coefficientCheck0100 :
    completeCoefficientRowCheck factorRow row0100 100 coefficients0100 = true := by
  have hlen : coefficients0100.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0100 oddDots0100
      641 100 0 coefficients0100 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0100_checked oddSum0100_checked hlen hs

theorem coefficientCheck0101 :
    completeCoefficientRowCheck factorRow row0101 101 coefficients0101 = true := by
  have hlen : coefficients0101.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0101 oddDots0101
      641 101 0 coefficients0101 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0101_checked oddSum0101_checked hlen hs

theorem coefficientCheck0102 :
    completeCoefficientRowCheck factorRow row0102 102 coefficients0102 = true := by
  have hlen : coefficients0102.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0102 oddDots0102
      641 102 0 coefficients0102 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0102_checked oddSum0102_checked hlen hs

theorem coefficientCheck0103 :
    completeCoefficientRowCheck factorRow row0103 103 coefficients0103 = true := by
  have hlen : coefficients0103.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0103 oddDots0103
      641 103 0 coefficients0103 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0103_checked oddSum0103_checked hlen hs


end
end ErdosOverlap.Native6Grid
