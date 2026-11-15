module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck014
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0112 :
    completeCoefficientRowCheck factorRow row0112 112 coefficients0112 = true := by
  have hlen : coefficients0112.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0112 oddDots0112
      641 112 0 coefficients0112 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0112_checked oddSum0112_checked hlen hs

theorem coefficientCheck0113 :
    completeCoefficientRowCheck factorRow row0113 113 coefficients0113 = true := by
  have hlen : coefficients0113.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0113 oddDots0113
      641 113 0 coefficients0113 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0113_checked oddSum0113_checked hlen hs

theorem coefficientCheck0114 :
    completeCoefficientRowCheck factorRow row0114 114 coefficients0114 = true := by
  have hlen : coefficients0114.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0114 oddDots0114
      641 114 0 coefficients0114 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0114_checked oddSum0114_checked hlen hs

theorem coefficientCheck0115 :
    completeCoefficientRowCheck factorRow row0115 115 coefficients0115 = true := by
  have hlen : coefficients0115.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0115 oddDots0115
      641 115 0 coefficients0115 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0115_checked oddSum0115_checked hlen hs

theorem coefficientCheck0116 :
    completeCoefficientRowCheck factorRow row0116 116 coefficients0116 = true := by
  have hlen : coefficients0116.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0116 oddDots0116
      641 116 0 coefficients0116 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0116_checked oddSum0116_checked hlen hs

theorem coefficientCheck0117 :
    completeCoefficientRowCheck factorRow row0117 117 coefficients0117 = true := by
  have hlen : coefficients0117.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0117 oddDots0117
      641 117 0 coefficients0117 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0117_checked oddSum0117_checked hlen hs

theorem coefficientCheck0118 :
    completeCoefficientRowCheck factorRow row0118 118 coefficients0118 = true := by
  have hlen : coefficients0118.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0118 oddDots0118
      641 118 0 coefficients0118 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0118_checked oddSum0118_checked hlen hs

theorem coefficientCheck0119 :
    completeCoefficientRowCheck factorRow row0119 119 coefficients0119 = true := by
  have hlen : coefficients0119.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0119 oddDots0119
      641 119 0 coefficients0119 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0119_checked oddSum0119_checked hlen hs


end
end ErdosOverlap.Native6Grid
