module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck010
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0080 :
    completeCoefficientRowCheck factorRow row0080 80 coefficients0080 = true := by
  have hlen : coefficients0080.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0080 oddDots0080
      641 80 0 coefficients0080 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0080_checked oddSum0080_checked hlen hs

theorem coefficientCheck0081 :
    completeCoefficientRowCheck factorRow row0081 81 coefficients0081 = true := by
  have hlen : coefficients0081.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0081 oddDots0081
      641 81 0 coefficients0081 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0081_checked oddSum0081_checked hlen hs

theorem coefficientCheck0082 :
    completeCoefficientRowCheck factorRow row0082 82 coefficients0082 = true := by
  have hlen : coefficients0082.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0082 oddDots0082
      641 82 0 coefficients0082 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0082_checked oddSum0082_checked hlen hs

theorem coefficientCheck0083 :
    completeCoefficientRowCheck factorRow row0083 83 coefficients0083 = true := by
  have hlen : coefficients0083.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0083 oddDots0083
      641 83 0 coefficients0083 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0083_checked oddSum0083_checked hlen hs

theorem coefficientCheck0084 :
    completeCoefficientRowCheck factorRow row0084 84 coefficients0084 = true := by
  have hlen : coefficients0084.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0084 oddDots0084
      641 84 0 coefficients0084 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0084_checked oddSum0084_checked hlen hs

theorem coefficientCheck0085 :
    completeCoefficientRowCheck factorRow row0085 85 coefficients0085 = true := by
  have hlen : coefficients0085.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0085 oddDots0085
      641 85 0 coefficients0085 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0085_checked oddSum0085_checked hlen hs

theorem coefficientCheck0086 :
    completeCoefficientRowCheck factorRow row0086 86 coefficients0086 = true := by
  have hlen : coefficients0086.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0086 oddDots0086
      641 86 0 coefficients0086 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0086_checked oddSum0086_checked hlen hs

theorem coefficientCheck0087 :
    completeCoefficientRowCheck factorRow row0087 87 coefficients0087 = true := by
  have hlen : coefficients0087.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0087 oddDots0087
      641 87 0 coefficients0087 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0087_checked oddSum0087_checked hlen hs


end
end ErdosOverlap.Native6Grid
