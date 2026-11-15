module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck117
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0936 :
    completeCoefficientRowCheck factorRow row0936 936 coefficients0936 = true := by
  have hlen : coefficients0936.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0936 oddDots0936
      641 936 0 coefficients0936 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0936_checked oddSum0936_checked hlen hs

theorem coefficientCheck0937 :
    completeCoefficientRowCheck factorRow row0937 937 coefficients0937 = true := by
  have hlen : coefficients0937.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0937 oddDots0937
      641 937 0 coefficients0937 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0937_checked oddSum0937_checked hlen hs

theorem coefficientCheck0938 :
    completeCoefficientRowCheck factorRow row0938 938 coefficients0938 = true := by
  have hlen : coefficients0938.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0938 oddDots0938
      641 938 0 coefficients0938 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0938_checked oddSum0938_checked hlen hs

theorem coefficientCheck0939 :
    completeCoefficientRowCheck factorRow row0939 939 coefficients0939 = true := by
  have hlen : coefficients0939.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0939 oddDots0939
      641 939 0 coefficients0939 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0939_checked oddSum0939_checked hlen hs

theorem coefficientCheck0940 :
    completeCoefficientRowCheck factorRow row0940 940 coefficients0940 = true := by
  have hlen : coefficients0940.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0940 oddDots0940
      641 940 0 coefficients0940 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0940_checked oddSum0940_checked hlen hs

theorem coefficientCheck0941 :
    completeCoefficientRowCheck factorRow row0941 941 coefficients0941 = true := by
  have hlen : coefficients0941.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0941 oddDots0941
      641 941 0 coefficients0941 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0941_checked oddSum0941_checked hlen hs

theorem coefficientCheck0942 :
    completeCoefficientRowCheck factorRow row0942 942 coefficients0942 = true := by
  have hlen : coefficients0942.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0942 oddDots0942
      641 942 0 coefficients0942 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0942_checked oddSum0942_checked hlen hs

theorem coefficientCheck0943 :
    completeCoefficientRowCheck factorRow row0943 943 coefficients0943 = true := by
  have hlen : coefficients0943.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0943 oddDots0943
      641 943 0 coefficients0943 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0943_checked oddSum0943_checked hlen hs


end
end ErdosOverlap.Native6Grid
