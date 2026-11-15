module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck034
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0272 :
    completeCoefficientRowCheck factorRow row0272 272 coefficients0272 = true := by
  have hlen : coefficients0272.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0272 oddDots0272
      641 272 0 coefficients0272 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0272_checked oddSum0272_checked hlen hs

theorem coefficientCheck0273 :
    completeCoefficientRowCheck factorRow row0273 273 coefficients0273 = true := by
  have hlen : coefficients0273.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0273 oddDots0273
      641 273 0 coefficients0273 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0273_checked oddSum0273_checked hlen hs

theorem coefficientCheck0274 :
    completeCoefficientRowCheck factorRow row0274 274 coefficients0274 = true := by
  have hlen : coefficients0274.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0274 oddDots0274
      641 274 0 coefficients0274 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0274_checked oddSum0274_checked hlen hs

theorem coefficientCheck0275 :
    completeCoefficientRowCheck factorRow row0275 275 coefficients0275 = true := by
  have hlen : coefficients0275.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0275 oddDots0275
      641 275 0 coefficients0275 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0275_checked oddSum0275_checked hlen hs

theorem coefficientCheck0276 :
    completeCoefficientRowCheck factorRow row0276 276 coefficients0276 = true := by
  have hlen : coefficients0276.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0276 oddDots0276
      641 276 0 coefficients0276 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0276_checked oddSum0276_checked hlen hs

theorem coefficientCheck0277 :
    completeCoefficientRowCheck factorRow row0277 277 coefficients0277 = true := by
  have hlen : coefficients0277.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0277 oddDots0277
      641 277 0 coefficients0277 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0277_checked oddSum0277_checked hlen hs

theorem coefficientCheck0278 :
    completeCoefficientRowCheck factorRow row0278 278 coefficients0278 = true := by
  have hlen : coefficients0278.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0278 oddDots0278
      641 278 0 coefficients0278 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0278_checked oddSum0278_checked hlen hs

theorem coefficientCheck0279 :
    completeCoefficientRowCheck factorRow row0279 279 coefficients0279 = true := by
  have hlen : coefficients0279.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0279 oddDots0279
      641 279 0 coefficients0279 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0279_checked oddSum0279_checked hlen hs


end
end ErdosOverlap.Native6Grid
