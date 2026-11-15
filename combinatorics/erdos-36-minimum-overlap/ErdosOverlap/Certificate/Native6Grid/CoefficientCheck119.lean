module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck119
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0952 :
    completeCoefficientRowCheck factorRow row0952 952 coefficients0952 = true := by
  have hlen : coefficients0952.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0952 oddDots0952
      641 952 0 coefficients0952 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0952_checked oddSum0952_checked hlen hs

theorem coefficientCheck0953 :
    completeCoefficientRowCheck factorRow row0953 953 coefficients0953 = true := by
  have hlen : coefficients0953.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0953 oddDots0953
      641 953 0 coefficients0953 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0953_checked oddSum0953_checked hlen hs

theorem coefficientCheck0954 :
    completeCoefficientRowCheck factorRow row0954 954 coefficients0954 = true := by
  have hlen : coefficients0954.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0954 oddDots0954
      641 954 0 coefficients0954 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0954_checked oddSum0954_checked hlen hs

theorem coefficientCheck0955 :
    completeCoefficientRowCheck factorRow row0955 955 coefficients0955 = true := by
  have hlen : coefficients0955.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0955 oddDots0955
      641 955 0 coefficients0955 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0955_checked oddSum0955_checked hlen hs

theorem coefficientCheck0956 :
    completeCoefficientRowCheck factorRow row0956 956 coefficients0956 = true := by
  have hlen : coefficients0956.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0956 oddDots0956
      641 956 0 coefficients0956 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0956_checked oddSum0956_checked hlen hs

theorem coefficientCheck0957 :
    completeCoefficientRowCheck factorRow row0957 957 coefficients0957 = true := by
  have hlen : coefficients0957.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0957 oddDots0957
      641 957 0 coefficients0957 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0957_checked oddSum0957_checked hlen hs

theorem coefficientCheck0958 :
    completeCoefficientRowCheck factorRow row0958 958 coefficients0958 = true := by
  have hlen : coefficients0958.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0958 oddDots0958
      641 958 0 coefficients0958 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0958_checked oddSum0958_checked hlen hs

theorem coefficientCheck0959 :
    completeCoefficientRowCheck factorRow row0959 959 coefficients0959 = true := by
  have hlen : coefficients0959.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0959 oddDots0959
      641 959 0 coefficients0959 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0959_checked oddSum0959_checked hlen hs


end
end ErdosOverlap.Native6Grid
