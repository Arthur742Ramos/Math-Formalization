module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck016
public import ErdosOverlap.Certificate.Native6Grid.Coefficients02

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0128 :
    completeCoefficientRowCheck factorRow row0128 128 coefficients0128 = true := by
  have hlen : coefficients0128.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0128 oddDots0128
      641 128 0 coefficients0128 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0128_checked oddSum0128_checked hlen hs

theorem coefficientCheck0129 :
    completeCoefficientRowCheck factorRow row0129 129 coefficients0129 = true := by
  have hlen : coefficients0129.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0129 oddDots0129
      641 129 0 coefficients0129 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0129_checked oddSum0129_checked hlen hs

theorem coefficientCheck0130 :
    completeCoefficientRowCheck factorRow row0130 130 coefficients0130 = true := by
  have hlen : coefficients0130.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0130 oddDots0130
      641 130 0 coefficients0130 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0130_checked oddSum0130_checked hlen hs

theorem coefficientCheck0131 :
    completeCoefficientRowCheck factorRow row0131 131 coefficients0131 = true := by
  have hlen : coefficients0131.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0131 oddDots0131
      641 131 0 coefficients0131 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0131_checked oddSum0131_checked hlen hs

theorem coefficientCheck0132 :
    completeCoefficientRowCheck factorRow row0132 132 coefficients0132 = true := by
  have hlen : coefficients0132.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0132 oddDots0132
      641 132 0 coefficients0132 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0132_checked oddSum0132_checked hlen hs

theorem coefficientCheck0133 :
    completeCoefficientRowCheck factorRow row0133 133 coefficients0133 = true := by
  have hlen : coefficients0133.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0133 oddDots0133
      641 133 0 coefficients0133 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0133_checked oddSum0133_checked hlen hs

theorem coefficientCheck0134 :
    completeCoefficientRowCheck factorRow row0134 134 coefficients0134 = true := by
  have hlen : coefficients0134.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0134 oddDots0134
      641 134 0 coefficients0134 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0134_checked oddSum0134_checked hlen hs

theorem coefficientCheck0135 :
    completeCoefficientRowCheck factorRow row0135 135 coefficients0135 = true := by
  have hlen : coefficients0135.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0135 oddDots0135
      641 135 0 coefficients0135 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0135_checked oddSum0135_checked hlen hs


end
end ErdosOverlap.Native6Grid
