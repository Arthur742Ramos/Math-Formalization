module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck121
public import ErdosOverlap.Certificate.Native6Grid.Coefficients15

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0968 :
    completeCoefficientRowCheck factorRow row0968 968 coefficients0968 = true := by
  have hlen : coefficients0968.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0968 oddDots0968
      641 968 0 coefficients0968 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0968_checked oddSum0968_checked hlen hs

theorem coefficientCheck0969 :
    completeCoefficientRowCheck factorRow row0969 969 coefficients0969 = true := by
  have hlen : coefficients0969.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0969 oddDots0969
      641 969 0 coefficients0969 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0969_checked oddSum0969_checked hlen hs

theorem coefficientCheck0970 :
    completeCoefficientRowCheck factorRow row0970 970 coefficients0970 = true := by
  have hlen : coefficients0970.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0970 oddDots0970
      641 970 0 coefficients0970 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0970_checked oddSum0970_checked hlen hs

theorem coefficientCheck0971 :
    completeCoefficientRowCheck factorRow row0971 971 coefficients0971 = true := by
  have hlen : coefficients0971.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0971 oddDots0971
      641 971 0 coefficients0971 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0971_checked oddSum0971_checked hlen hs

theorem coefficientCheck0972 :
    completeCoefficientRowCheck factorRow row0972 972 coefficients0972 = true := by
  have hlen : coefficients0972.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0972 oddDots0972
      641 972 0 coefficients0972 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0972_checked oddSum0972_checked hlen hs

theorem coefficientCheck0973 :
    completeCoefficientRowCheck factorRow row0973 973 coefficients0973 = true := by
  have hlen : coefficients0973.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0973 oddDots0973
      641 973 0 coefficients0973 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0973_checked oddSum0973_checked hlen hs

theorem coefficientCheck0974 :
    completeCoefficientRowCheck factorRow row0974 974 coefficients0974 = true := by
  have hlen : coefficients0974.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0974 oddDots0974
      641 974 0 coefficients0974 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0974_checked oddSum0974_checked hlen hs

theorem coefficientCheck0975 :
    completeCoefficientRowCheck factorRow row0975 975 coefficients0975 = true := by
  have hlen : coefficients0975.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0975 oddDots0975
      641 975 0 coefficients0975 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0975_checked oddSum0975_checked hlen hs


end
end ErdosOverlap.Native6Grid
