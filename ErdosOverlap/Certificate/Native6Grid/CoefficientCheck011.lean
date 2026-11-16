module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck011
public import ErdosOverlap.Certificate.Native6Grid.Coefficients01

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0088 :
    completeCoefficientRowCheck factorRow row0088 88 coefficients0088 = true := by
  have hlen : coefficients0088.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0088 oddDots0088
      641 88 0 coefficients0088 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0088_checked oddSum0088_checked hlen hs

theorem coefficientCheck0089 :
    completeCoefficientRowCheck factorRow row0089 89 coefficients0089 = true := by
  have hlen : coefficients0089.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0089 oddDots0089
      641 89 0 coefficients0089 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0089_checked oddSum0089_checked hlen hs

theorem coefficientCheck0090 :
    completeCoefficientRowCheck factorRow row0090 90 coefficients0090 = true := by
  have hlen : coefficients0090.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0090 oddDots0090
      641 90 0 coefficients0090 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0090_checked oddSum0090_checked hlen hs

theorem coefficientCheck0091 :
    completeCoefficientRowCheck factorRow row0091 91 coefficients0091 = true := by
  have hlen : coefficients0091.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0091 oddDots0091
      641 91 0 coefficients0091 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0091_checked oddSum0091_checked hlen hs

theorem coefficientCheck0092 :
    completeCoefficientRowCheck factorRow row0092 92 coefficients0092 = true := by
  have hlen : coefficients0092.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0092 oddDots0092
      641 92 0 coefficients0092 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0092_checked oddSum0092_checked hlen hs

theorem coefficientCheck0093 :
    completeCoefficientRowCheck factorRow row0093 93 coefficients0093 = true := by
  have hlen : coefficients0093.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0093 oddDots0093
      641 93 0 coefficients0093 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0093_checked oddSum0093_checked hlen hs

theorem coefficientCheck0094 :
    completeCoefficientRowCheck factorRow row0094 94 coefficients0094 = true := by
  have hlen : coefficients0094.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0094 oddDots0094
      641 94 0 coefficients0094 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0094_checked oddSum0094_checked hlen hs

theorem coefficientCheck0095 :
    completeCoefficientRowCheck factorRow row0095 95 coefficients0095 = true := by
  have hlen : coefficients0095.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0095 oddDots0095
      641 95 0 coefficients0095 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0095_checked oddSum0095_checked hlen hs


end
end ErdosOverlap.Native6Grid
