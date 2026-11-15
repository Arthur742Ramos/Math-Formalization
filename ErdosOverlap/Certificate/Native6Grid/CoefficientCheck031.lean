module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck031
public import ErdosOverlap.Certificate.Native6Grid.Coefficients03

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0248 :
    completeCoefficientRowCheck factorRow row0248 248 coefficients0248 = true := by
  have hlen : coefficients0248.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0248 oddDots0248
      641 248 0 coefficients0248 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0248_checked oddSum0248_checked hlen hs

theorem coefficientCheck0249 :
    completeCoefficientRowCheck factorRow row0249 249 coefficients0249 = true := by
  have hlen : coefficients0249.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0249 oddDots0249
      641 249 0 coefficients0249 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0249_checked oddSum0249_checked hlen hs

theorem coefficientCheck0250 :
    completeCoefficientRowCheck factorRow row0250 250 coefficients0250 = true := by
  have hlen : coefficients0250.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0250 oddDots0250
      641 250 0 coefficients0250 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0250_checked oddSum0250_checked hlen hs

theorem coefficientCheck0251 :
    completeCoefficientRowCheck factorRow row0251 251 coefficients0251 = true := by
  have hlen : coefficients0251.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0251 oddDots0251
      641 251 0 coefficients0251 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0251_checked oddSum0251_checked hlen hs

theorem coefficientCheck0252 :
    completeCoefficientRowCheck factorRow row0252 252 coefficients0252 = true := by
  have hlen : coefficients0252.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0252 oddDots0252
      641 252 0 coefficients0252 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0252_checked oddSum0252_checked hlen hs

theorem coefficientCheck0253 :
    completeCoefficientRowCheck factorRow row0253 253 coefficients0253 = true := by
  have hlen : coefficients0253.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0253 oddDots0253
      641 253 0 coefficients0253 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0253_checked oddSum0253_checked hlen hs

theorem coefficientCheck0254 :
    completeCoefficientRowCheck factorRow row0254 254 coefficients0254 = true := by
  have hlen : coefficients0254.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0254 oddDots0254
      641 254 0 coefficients0254 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0254_checked oddSum0254_checked hlen hs

theorem coefficientCheck0255 :
    completeCoefficientRowCheck factorRow row0255 255 coefficients0255 = true := by
  have hlen : coefficients0255.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0255 oddDots0255
      641 255 0 coefficients0255 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0255_checked oddSum0255_checked hlen hs


end
end ErdosOverlap.Native6Grid
