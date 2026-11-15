module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck009
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0072 :
    completeCoefficientRowCheck factorRow row0072 72 coefficients0072 = true := by
  have hlen : coefficients0072.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0072 oddDots0072
      641 72 0 coefficients0072 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0072_checked oddSum0072_checked hlen hs

theorem coefficientCheck0073 :
    completeCoefficientRowCheck factorRow row0073 73 coefficients0073 = true := by
  have hlen : coefficients0073.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0073 oddDots0073
      641 73 0 coefficients0073 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0073_checked oddSum0073_checked hlen hs

theorem coefficientCheck0074 :
    completeCoefficientRowCheck factorRow row0074 74 coefficients0074 = true := by
  have hlen : coefficients0074.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0074 oddDots0074
      641 74 0 coefficients0074 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0074_checked oddSum0074_checked hlen hs

theorem coefficientCheck0075 :
    completeCoefficientRowCheck factorRow row0075 75 coefficients0075 = true := by
  have hlen : coefficients0075.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0075 oddDots0075
      641 75 0 coefficients0075 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0075_checked oddSum0075_checked hlen hs

theorem coefficientCheck0076 :
    completeCoefficientRowCheck factorRow row0076 76 coefficients0076 = true := by
  have hlen : coefficients0076.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0076 oddDots0076
      641 76 0 coefficients0076 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0076_checked oddSum0076_checked hlen hs

theorem coefficientCheck0077 :
    completeCoefficientRowCheck factorRow row0077 77 coefficients0077 = true := by
  have hlen : coefficients0077.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0077 oddDots0077
      641 77 0 coefficients0077 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0077_checked oddSum0077_checked hlen hs

theorem coefficientCheck0078 :
    completeCoefficientRowCheck factorRow row0078 78 coefficients0078 = true := by
  have hlen : coefficients0078.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0078 oddDots0078
      641 78 0 coefficients0078 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0078_checked oddSum0078_checked hlen hs

theorem coefficientCheck0079 :
    completeCoefficientRowCheck factorRow row0079 79 coefficients0079 = true := by
  have hlen : coefficients0079.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0079 oddDots0079
      641 79 0 coefficients0079 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0079_checked oddSum0079_checked hlen hs


end
end ErdosOverlap.Native6Grid
