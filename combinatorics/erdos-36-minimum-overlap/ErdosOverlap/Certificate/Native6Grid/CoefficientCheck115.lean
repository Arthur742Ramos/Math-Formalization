module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck115
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0920 :
    completeCoefficientRowCheck factorRow row0920 920 coefficients0920 = true := by
  have hlen : coefficients0920.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0920 oddDots0920
      641 920 0 coefficients0920 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0920_checked oddSum0920_checked hlen hs

theorem coefficientCheck0921 :
    completeCoefficientRowCheck factorRow row0921 921 coefficients0921 = true := by
  have hlen : coefficients0921.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0921 oddDots0921
      641 921 0 coefficients0921 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0921_checked oddSum0921_checked hlen hs

theorem coefficientCheck0922 :
    completeCoefficientRowCheck factorRow row0922 922 coefficients0922 = true := by
  have hlen : coefficients0922.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0922 oddDots0922
      641 922 0 coefficients0922 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0922_checked oddSum0922_checked hlen hs

theorem coefficientCheck0923 :
    completeCoefficientRowCheck factorRow row0923 923 coefficients0923 = true := by
  have hlen : coefficients0923.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0923 oddDots0923
      641 923 0 coefficients0923 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0923_checked oddSum0923_checked hlen hs

theorem coefficientCheck0924 :
    completeCoefficientRowCheck factorRow row0924 924 coefficients0924 = true := by
  have hlen : coefficients0924.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0924 oddDots0924
      641 924 0 coefficients0924 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0924_checked oddSum0924_checked hlen hs

theorem coefficientCheck0925 :
    completeCoefficientRowCheck factorRow row0925 925 coefficients0925 = true := by
  have hlen : coefficients0925.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0925 oddDots0925
      641 925 0 coefficients0925 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0925_checked oddSum0925_checked hlen hs

theorem coefficientCheck0926 :
    completeCoefficientRowCheck factorRow row0926 926 coefficients0926 = true := by
  have hlen : coefficients0926.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0926 oddDots0926
      641 926 0 coefficients0926 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0926_checked oddSum0926_checked hlen hs

theorem coefficientCheck0927 :
    completeCoefficientRowCheck factorRow row0927 927 coefficients0927 = true := by
  have hlen : coefficients0927.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0927 oddDots0927
      641 927 0 coefficients0927 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0927_checked oddSum0927_checked hlen hs


end
end ErdosOverlap.Native6Grid
