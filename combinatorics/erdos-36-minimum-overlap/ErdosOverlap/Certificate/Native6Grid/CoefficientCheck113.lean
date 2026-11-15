module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck113
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0904 :
    completeCoefficientRowCheck factorRow row0904 904 coefficients0904 = true := by
  have hlen : coefficients0904.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0904 oddDots0904
      641 904 0 coefficients0904 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0904_checked oddSum0904_checked hlen hs

theorem coefficientCheck0905 :
    completeCoefficientRowCheck factorRow row0905 905 coefficients0905 = true := by
  have hlen : coefficients0905.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0905 oddDots0905
      641 905 0 coefficients0905 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0905_checked oddSum0905_checked hlen hs

theorem coefficientCheck0906 :
    completeCoefficientRowCheck factorRow row0906 906 coefficients0906 = true := by
  have hlen : coefficients0906.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0906 oddDots0906
      641 906 0 coefficients0906 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0906_checked oddSum0906_checked hlen hs

theorem coefficientCheck0907 :
    completeCoefficientRowCheck factorRow row0907 907 coefficients0907 = true := by
  have hlen : coefficients0907.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0907 oddDots0907
      641 907 0 coefficients0907 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0907_checked oddSum0907_checked hlen hs

theorem coefficientCheck0908 :
    completeCoefficientRowCheck factorRow row0908 908 coefficients0908 = true := by
  have hlen : coefficients0908.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0908 oddDots0908
      641 908 0 coefficients0908 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0908_checked oddSum0908_checked hlen hs

theorem coefficientCheck0909 :
    completeCoefficientRowCheck factorRow row0909 909 coefficients0909 = true := by
  have hlen : coefficients0909.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0909 oddDots0909
      641 909 0 coefficients0909 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0909_checked oddSum0909_checked hlen hs

theorem coefficientCheck0910 :
    completeCoefficientRowCheck factorRow row0910 910 coefficients0910 = true := by
  have hlen : coefficients0910.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0910 oddDots0910
      641 910 0 coefficients0910 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0910_checked oddSum0910_checked hlen hs

theorem coefficientCheck0911 :
    completeCoefficientRowCheck factorRow row0911 911 coefficients0911 = true := by
  have hlen : coefficients0911.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0911 oddDots0911
      641 911 0 coefficients0911 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0911_checked oddSum0911_checked hlen hs


end
end ErdosOverlap.Native6Grid
