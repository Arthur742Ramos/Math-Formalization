module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck038
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0304 :
    completeCoefficientRowCheck factorRow row0304 304 coefficients0304 = true := by
  have hlen : coefficients0304.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0304 oddDots0304
      641 304 0 coefficients0304 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0304_checked oddSum0304_checked hlen hs

theorem coefficientCheck0305 :
    completeCoefficientRowCheck factorRow row0305 305 coefficients0305 = true := by
  have hlen : coefficients0305.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0305 oddDots0305
      641 305 0 coefficients0305 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0305_checked oddSum0305_checked hlen hs

theorem coefficientCheck0306 :
    completeCoefficientRowCheck factorRow row0306 306 coefficients0306 = true := by
  have hlen : coefficients0306.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0306 oddDots0306
      641 306 0 coefficients0306 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0306_checked oddSum0306_checked hlen hs

theorem coefficientCheck0307 :
    completeCoefficientRowCheck factorRow row0307 307 coefficients0307 = true := by
  have hlen : coefficients0307.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0307 oddDots0307
      641 307 0 coefficients0307 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0307_checked oddSum0307_checked hlen hs

theorem coefficientCheck0308 :
    completeCoefficientRowCheck factorRow row0308 308 coefficients0308 = true := by
  have hlen : coefficients0308.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0308 oddDots0308
      641 308 0 coefficients0308 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0308_checked oddSum0308_checked hlen hs

theorem coefficientCheck0309 :
    completeCoefficientRowCheck factorRow row0309 309 coefficients0309 = true := by
  have hlen : coefficients0309.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0309 oddDots0309
      641 309 0 coefficients0309 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0309_checked oddSum0309_checked hlen hs

theorem coefficientCheck0310 :
    completeCoefficientRowCheck factorRow row0310 310 coefficients0310 = true := by
  have hlen : coefficients0310.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0310 oddDots0310
      641 310 0 coefficients0310 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0310_checked oddSum0310_checked hlen hs

theorem coefficientCheck0311 :
    completeCoefficientRowCheck factorRow row0311 311 coefficients0311 = true := by
  have hlen : coefficients0311.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0311 oddDots0311
      641 311 0 coefficients0311 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0311_checked oddSum0311_checked hlen hs


end
end ErdosOverlap.Native6Grid
