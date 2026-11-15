module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck015
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0120 :
    completeCoefficientRowCheck factorRow row0120 120 coefficients0120 = true := by
  have hlen : coefficients0120.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0120 oddDots0120
      641 120 0 coefficients0120 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0120_checked oddSum0120_checked hlen hs

theorem coefficientCheck0121 :
    completeCoefficientRowCheck factorRow row0121 121 coefficients0121 = true := by
  have hlen : coefficients0121.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0121 oddDots0121
      641 121 0 coefficients0121 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0121_checked oddSum0121_checked hlen hs

theorem coefficientCheck0122 :
    completeCoefficientRowCheck factorRow row0122 122 coefficients0122 = true := by
  have hlen : coefficients0122.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0122 oddDots0122
      641 122 0 coefficients0122 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0122_checked oddSum0122_checked hlen hs

theorem coefficientCheck0123 :
    completeCoefficientRowCheck factorRow row0123 123 coefficients0123 = true := by
  have hlen : coefficients0123.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0123 oddDots0123
      641 123 0 coefficients0123 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0123_checked oddSum0123_checked hlen hs

theorem coefficientCheck0124 :
    completeCoefficientRowCheck factorRow row0124 124 coefficients0124 = true := by
  have hlen : coefficients0124.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0124 oddDots0124
      641 124 0 coefficients0124 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0124_checked oddSum0124_checked hlen hs

theorem coefficientCheck0125 :
    completeCoefficientRowCheck factorRow row0125 125 coefficients0125 = true := by
  have hlen : coefficients0125.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0125 oddDots0125
      641 125 0 coefficients0125 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0125_checked oddSum0125_checked hlen hs

theorem coefficientCheck0126 :
    completeCoefficientRowCheck factorRow row0126 126 coefficients0126 = true := by
  have hlen : coefficients0126.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0126 oddDots0126
      641 126 0 coefficients0126 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0126_checked oddSum0126_checked hlen hs

theorem coefficientCheck0127 :
    completeCoefficientRowCheck factorRow row0127 127 coefficients0127 = true := by
  have hlen : coefficients0127.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0127 oddDots0127
      641 127 0 coefficients0127 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0127_checked oddSum0127_checked hlen hs


end
end ErdosOverlap.Native6Grid
