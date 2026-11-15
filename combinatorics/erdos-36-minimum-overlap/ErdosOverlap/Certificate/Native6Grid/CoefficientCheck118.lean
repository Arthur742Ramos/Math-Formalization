module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck118
public import ErdosOverlap.Certificate.Native6Grid.Coefficients14

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0944 :
    completeCoefficientRowCheck factorRow row0944 944 coefficients0944 = true := by
  have hlen : coefficients0944.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0944 oddDots0944
      641 944 0 coefficients0944 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0944_checked oddSum0944_checked hlen hs

theorem coefficientCheck0945 :
    completeCoefficientRowCheck factorRow row0945 945 coefficients0945 = true := by
  have hlen : coefficients0945.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0945 oddDots0945
      641 945 0 coefficients0945 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0945_checked oddSum0945_checked hlen hs

theorem coefficientCheck0946 :
    completeCoefficientRowCheck factorRow row0946 946 coefficients0946 = true := by
  have hlen : coefficients0946.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0946 oddDots0946
      641 946 0 coefficients0946 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0946_checked oddSum0946_checked hlen hs

theorem coefficientCheck0947 :
    completeCoefficientRowCheck factorRow row0947 947 coefficients0947 = true := by
  have hlen : coefficients0947.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0947 oddDots0947
      641 947 0 coefficients0947 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0947_checked oddSum0947_checked hlen hs

theorem coefficientCheck0948 :
    completeCoefficientRowCheck factorRow row0948 948 coefficients0948 = true := by
  have hlen : coefficients0948.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0948 oddDots0948
      641 948 0 coefficients0948 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0948_checked oddSum0948_checked hlen hs

theorem coefficientCheck0949 :
    completeCoefficientRowCheck factorRow row0949 949 coefficients0949 = true := by
  have hlen : coefficients0949.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0949 oddDots0949
      641 949 0 coefficients0949 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0949_checked oddSum0949_checked hlen hs

theorem coefficientCheck0950 :
    completeCoefficientRowCheck factorRow row0950 950 coefficients0950 = true := by
  have hlen : coefficients0950.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0950 oddDots0950
      641 950 0 coefficients0950 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0950_checked oddSum0950_checked hlen hs

theorem coefficientCheck0951 :
    completeCoefficientRowCheck factorRow row0951 951 coefficients0951 = true := by
  have hlen : coefficients0951.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0951 oddDots0951
      641 951 0 coefficients0951 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0951_checked oddSum0951_checked hlen hs


end
end ErdosOverlap.Native6Grid
