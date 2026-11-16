module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck036
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0288 :
    completeCoefficientRowCheck factorRow row0288 288 coefficients0288 = true := by
  have hlen : coefficients0288.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0288 oddDots0288
      641 288 0 coefficients0288 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0288_checked oddSum0288_checked hlen hs

theorem coefficientCheck0289 :
    completeCoefficientRowCheck factorRow row0289 289 coefficients0289 = true := by
  have hlen : coefficients0289.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0289 oddDots0289
      641 289 0 coefficients0289 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0289_checked oddSum0289_checked hlen hs

theorem coefficientCheck0290 :
    completeCoefficientRowCheck factorRow row0290 290 coefficients0290 = true := by
  have hlen : coefficients0290.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0290 oddDots0290
      641 290 0 coefficients0290 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0290_checked oddSum0290_checked hlen hs

theorem coefficientCheck0291 :
    completeCoefficientRowCheck factorRow row0291 291 coefficients0291 = true := by
  have hlen : coefficients0291.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0291 oddDots0291
      641 291 0 coefficients0291 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0291_checked oddSum0291_checked hlen hs

theorem coefficientCheck0292 :
    completeCoefficientRowCheck factorRow row0292 292 coefficients0292 = true := by
  have hlen : coefficients0292.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0292 oddDots0292
      641 292 0 coefficients0292 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0292_checked oddSum0292_checked hlen hs

theorem coefficientCheck0293 :
    completeCoefficientRowCheck factorRow row0293 293 coefficients0293 = true := by
  have hlen : coefficients0293.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0293 oddDots0293
      641 293 0 coefficients0293 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0293_checked oddSum0293_checked hlen hs

theorem coefficientCheck0294 :
    completeCoefficientRowCheck factorRow row0294 294 coefficients0294 = true := by
  have hlen : coefficients0294.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0294 oddDots0294
      641 294 0 coefficients0294 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0294_checked oddSum0294_checked hlen hs

theorem coefficientCheck0295 :
    completeCoefficientRowCheck factorRow row0295 295 coefficients0295 = true := by
  have hlen : coefficients0295.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0295 oddDots0295
      641 295 0 coefficients0295 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0295_checked oddSum0295_checked hlen hs


end
end ErdosOverlap.Native6Grid
