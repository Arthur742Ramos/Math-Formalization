module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck033
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0264 :
    completeCoefficientRowCheck factorRow row0264 264 coefficients0264 = true := by
  have hlen : coefficients0264.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0264 oddDots0264
      641 264 0 coefficients0264 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0264_checked oddSum0264_checked hlen hs

theorem coefficientCheck0265 :
    completeCoefficientRowCheck factorRow row0265 265 coefficients0265 = true := by
  have hlen : coefficients0265.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0265 oddDots0265
      641 265 0 coefficients0265 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0265_checked oddSum0265_checked hlen hs

theorem coefficientCheck0266 :
    completeCoefficientRowCheck factorRow row0266 266 coefficients0266 = true := by
  have hlen : coefficients0266.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0266 oddDots0266
      641 266 0 coefficients0266 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0266_checked oddSum0266_checked hlen hs

theorem coefficientCheck0267 :
    completeCoefficientRowCheck factorRow row0267 267 coefficients0267 = true := by
  have hlen : coefficients0267.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0267 oddDots0267
      641 267 0 coefficients0267 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0267_checked oddSum0267_checked hlen hs

theorem coefficientCheck0268 :
    completeCoefficientRowCheck factorRow row0268 268 coefficients0268 = true := by
  have hlen : coefficients0268.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0268 oddDots0268
      641 268 0 coefficients0268 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0268_checked oddSum0268_checked hlen hs

theorem coefficientCheck0269 :
    completeCoefficientRowCheck factorRow row0269 269 coefficients0269 = true := by
  have hlen : coefficients0269.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0269 oddDots0269
      641 269 0 coefficients0269 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0269_checked oddSum0269_checked hlen hs

theorem coefficientCheck0270 :
    completeCoefficientRowCheck factorRow row0270 270 coefficients0270 = true := by
  have hlen : coefficients0270.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0270 oddDots0270
      641 270 0 coefficients0270 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0270_checked oddSum0270_checked hlen hs

theorem coefficientCheck0271 :
    completeCoefficientRowCheck factorRow row0271 271 coefficients0271 = true := by
  have hlen : coefficients0271.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0271 oddDots0271
      641 271 0 coefficients0271 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0271_checked oddSum0271_checked hlen hs


end
end ErdosOverlap.Native6Grid
