module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck002
public import ErdosOverlap.Certificate.Native6Grid.Coefficients00

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0016 :
    completeCoefficientRowCheck factorRow row0016 16 coefficients0016 = true := by
  have hlen : coefficients0016.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0016 oddDots0016
      641 16 0 coefficients0016 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0016_checked oddSum0016_checked hlen hs

theorem coefficientCheck0017 :
    completeCoefficientRowCheck factorRow row0017 17 coefficients0017 = true := by
  have hlen : coefficients0017.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0017 oddDots0017
      641 17 0 coefficients0017 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0017_checked oddSum0017_checked hlen hs

theorem coefficientCheck0018 :
    completeCoefficientRowCheck factorRow row0018 18 coefficients0018 = true := by
  have hlen : coefficients0018.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0018 oddDots0018
      641 18 0 coefficients0018 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0018_checked oddSum0018_checked hlen hs

theorem coefficientCheck0019 :
    completeCoefficientRowCheck factorRow row0019 19 coefficients0019 = true := by
  have hlen : coefficients0019.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0019 oddDots0019
      641 19 0 coefficients0019 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0019_checked oddSum0019_checked hlen hs

theorem coefficientCheck0020 :
    completeCoefficientRowCheck factorRow row0020 20 coefficients0020 = true := by
  have hlen : coefficients0020.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0020 oddDots0020
      641 20 0 coefficients0020 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0020_checked oddSum0020_checked hlen hs

theorem coefficientCheck0021 :
    completeCoefficientRowCheck factorRow row0021 21 coefficients0021 = true := by
  have hlen : coefficients0021.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0021 oddDots0021
      641 21 0 coefficients0021 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0021_checked oddSum0021_checked hlen hs

theorem coefficientCheck0022 :
    completeCoefficientRowCheck factorRow row0022 22 coefficients0022 = true := by
  have hlen : coefficients0022.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0022 oddDots0022
      641 22 0 coefficients0022 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0022_checked oddSum0022_checked hlen hs

theorem coefficientCheck0023 :
    completeCoefficientRowCheck factorRow row0023 23 coefficients0023 = true := by
  have hlen : coefficients0023.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0023 oddDots0023
      641 23 0 coefficients0023 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0023_checked oddSum0023_checked hlen hs


end
end ErdosOverlap.Native6Grid
