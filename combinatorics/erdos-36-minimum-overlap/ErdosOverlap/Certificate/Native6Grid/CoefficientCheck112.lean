module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck112
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0896 :
    completeCoefficientRowCheck factorRow row0896 896 coefficients0896 = true := by
  have hlen : coefficients0896.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0896 oddDots0896
      641 896 0 coefficients0896 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0896_checked oddSum0896_checked hlen hs

theorem coefficientCheck0897 :
    completeCoefficientRowCheck factorRow row0897 897 coefficients0897 = true := by
  have hlen : coefficients0897.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0897 oddDots0897
      641 897 0 coefficients0897 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0897_checked oddSum0897_checked hlen hs

theorem coefficientCheck0898 :
    completeCoefficientRowCheck factorRow row0898 898 coefficients0898 = true := by
  have hlen : coefficients0898.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0898 oddDots0898
      641 898 0 coefficients0898 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0898_checked oddSum0898_checked hlen hs

theorem coefficientCheck0899 :
    completeCoefficientRowCheck factorRow row0899 899 coefficients0899 = true := by
  have hlen : coefficients0899.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0899 oddDots0899
      641 899 0 coefficients0899 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0899_checked oddSum0899_checked hlen hs

theorem coefficientCheck0900 :
    completeCoefficientRowCheck factorRow row0900 900 coefficients0900 = true := by
  have hlen : coefficients0900.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0900 oddDots0900
      641 900 0 coefficients0900 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0900_checked oddSum0900_checked hlen hs

theorem coefficientCheck0901 :
    completeCoefficientRowCheck factorRow row0901 901 coefficients0901 = true := by
  have hlen : coefficients0901.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0901 oddDots0901
      641 901 0 coefficients0901 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0901_checked oddSum0901_checked hlen hs

theorem coefficientCheck0902 :
    completeCoefficientRowCheck factorRow row0902 902 coefficients0902 = true := by
  have hlen : coefficients0902.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0902 oddDots0902
      641 902 0 coefficients0902 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0902_checked oddSum0902_checked hlen hs

theorem coefficientCheck0903 :
    completeCoefficientRowCheck factorRow row0903 903 coefficients0903 = true := by
  have hlen : coefficients0903.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0903 oddDots0903
      641 903 0 coefficients0903 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0903_checked oddSum0903_checked hlen hs


end
end ErdosOverlap.Native6Grid
