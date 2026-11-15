module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck109
public import ErdosOverlap.Certificate.Native6Grid.Coefficients13

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0872 :
    completeCoefficientRowCheck factorRow row0872 872 coefficients0872 = true := by
  have hlen : coefficients0872.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0872 oddDots0872
      641 872 0 coefficients0872 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0872_checked oddSum0872_checked hlen hs

theorem coefficientCheck0873 :
    completeCoefficientRowCheck factorRow row0873 873 coefficients0873 = true := by
  have hlen : coefficients0873.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0873 oddDots0873
      641 873 0 coefficients0873 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0873_checked oddSum0873_checked hlen hs

theorem coefficientCheck0874 :
    completeCoefficientRowCheck factorRow row0874 874 coefficients0874 = true := by
  have hlen : coefficients0874.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0874 oddDots0874
      641 874 0 coefficients0874 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0874_checked oddSum0874_checked hlen hs

theorem coefficientCheck0875 :
    completeCoefficientRowCheck factorRow row0875 875 coefficients0875 = true := by
  have hlen : coefficients0875.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0875 oddDots0875
      641 875 0 coefficients0875 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0875_checked oddSum0875_checked hlen hs

theorem coefficientCheck0876 :
    completeCoefficientRowCheck factorRow row0876 876 coefficients0876 = true := by
  have hlen : coefficients0876.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0876 oddDots0876
      641 876 0 coefficients0876 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0876_checked oddSum0876_checked hlen hs

theorem coefficientCheck0877 :
    completeCoefficientRowCheck factorRow row0877 877 coefficients0877 = true := by
  have hlen : coefficients0877.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0877 oddDots0877
      641 877 0 coefficients0877 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0877_checked oddSum0877_checked hlen hs

theorem coefficientCheck0878 :
    completeCoefficientRowCheck factorRow row0878 878 coefficients0878 = true := by
  have hlen : coefficients0878.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0878 oddDots0878
      641 878 0 coefficients0878 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0878_checked oddSum0878_checked hlen hs

theorem coefficientCheck0879 :
    completeCoefficientRowCheck factorRow row0879 879 coefficients0879 = true := by
  have hlen : coefficients0879.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0879 oddDots0879
      641 879 0 coefficients0879 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0879_checked oddSum0879_checked hlen hs


end
end ErdosOverlap.Native6Grid
