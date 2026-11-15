module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck127
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck1016 :
    completeCoefficientRowCheck factorRow row1016 1016 coefficients1016 = true := by
  have hlen : coefficients1016.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1016 oddDots1016
      641 1016 0 coefficients1016 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1016_checked oddSum1016_checked hlen hs

theorem coefficientCheck1017 :
    completeCoefficientRowCheck factorRow row1017 1017 coefficients1017 = true := by
  have hlen : coefficients1017.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1017 oddDots1017
      641 1017 0 coefficients1017 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1017_checked oddSum1017_checked hlen hs

theorem coefficientCheck1018 :
    completeCoefficientRowCheck factorRow row1018 1018 coefficients1018 = true := by
  have hlen : coefficients1018.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1018 oddDots1018
      641 1018 0 coefficients1018 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1018_checked oddSum1018_checked hlen hs

theorem coefficientCheck1019 :
    completeCoefficientRowCheck factorRow row1019 1019 coefficients1019 = true := by
  have hlen : coefficients1019.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1019 oddDots1019
      641 1019 0 coefficients1019 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1019_checked oddSum1019_checked hlen hs

theorem coefficientCheck1020 :
    completeCoefficientRowCheck factorRow row1020 1020 coefficients1020 = true := by
  have hlen : coefficients1020.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1020 oddDots1020
      641 1020 0 coefficients1020 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1020_checked oddSum1020_checked hlen hs

theorem coefficientCheck1021 :
    completeCoefficientRowCheck factorRow row1021 1021 coefficients1021 = true := by
  have hlen : coefficients1021.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1021 oddDots1021
      641 1021 0 coefficients1021 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1021_checked oddSum1021_checked hlen hs

theorem coefficientCheck1022 :
    completeCoefficientRowCheck factorRow row1022 1022 coefficients1022 = true := by
  have hlen : coefficients1022.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1022 oddDots1022
      641 1022 0 coefficients1022 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1022_checked oddSum1022_checked hlen hs

theorem coefficientCheck1023 :
    completeCoefficientRowCheck factorRow row1023 1023 coefficients1023 = true := by
  have hlen : coefficients1023.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots1023 oddDots1023
      641 1023 0 coefficients1023 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum1023_checked oddSum1023_checked hlen hs


end
end ErdosOverlap.Native6Grid
